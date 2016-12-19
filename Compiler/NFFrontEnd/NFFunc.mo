/*
 * This file is part of OpenModelica.
 *
 * Copyright (c) 1998-2014, Open Source Modelica Consortium (OSMC),
 * c/o Linköpings universitet, Department of Computer and Information Science,
 * SE-58183 Linköping, Sweden.
 *
 * All rights reserved.
 *
 * THIS PROGRAM IS PROVIDED UNDER THE TERMS OF GPL VERSION 3 LICENSE OR
 * THIS OSMC PUBLIC LICENSE (OSMC-PL) VERSION 1.2.
 * ANY USE, REPRODUCTION OR DISTRIBUTION OF THIS PROGRAM CONSTITUTES
 * RECIPIENT'S ACCEPTANCE OF THE OSMC PUBLIC LICENSE OR THE GPL VERSION 3,
 * ACCORDING TO RECIPIENTS CHOICE.
 *
 * The OpenModelica software and the Open Source Modelica
 * Consortium (OSMC) Public License (OSMC-PL) are obtained
 * from OSMC, either from the above address,
 * from the URLs: http://www.ida.liu.se/projects/OpenModelica or
 * http://www.openmodelica.org, and in the OpenModelica distribution.
 * GNU version 3 is obtained from: http://www.gnu.org/copyleft/gpl.html.
 *
 * This program is distributed WITHOUT ANY WARRANTY; without
 * even the implied warranty of  MERCHANTABILITY or FITNESS
 * FOR A PARTICULAR PURPOSE, EXCEPT AS EXPRESSLY SET FORTH
 * IN THE BY RECIPIENT SELECTED SUBSIDIARY LICENSE CONDITIONS OF OSMC-PL.
 *
 * See the full OSMC Public License conditions for more details.
 *
 */

encapsulated package NFFunc
" file:        NFFunc.mo
  package:     NFFunc
  description: package for handling functions.


  Functions used by NFInst for handling functions.
"

import NFBinding.Binding;
import NFComponent.Component;
import NFComponentNode.ComponentNode;
import NFDimension.Dimension;
import NFEquation.Equation;
import NFInstance.Instance;
import NFInstNode.InstNode;
import NFMod.Modifier;
import NFPrefix.Prefix;
import NFStatement.Statement;

protected
import ComponentReference;
import Error;
import Expression;
import ExpressionDump;
import Inst = NFInst;
import Lookup = NFLookup;
import TypeCheck = NFTypeCheck;
import Types;
import ClassInf;
import Static;
import NFInstUtil;
import NFTyping;
import NFRecord;
import List;
import InstUtil;

public
public uniontype FunctionSlot
  record SLOT
    String name "the name of the slot";
    Option<tuple<DAE.Exp, DAE.Type, DAE.Const>> arg "the argument given by the function call";
    Option<NFBinding.Binding> default "the default value from binding of the input component in the function";
    Option<tuple<DAE.Type, DAE.Const>> expected "the actual type of the input component, what we expect to get";
    Boolean isFilled;
  end SLOT;
end FunctionSlot;

public
function typeFunctionCall
  input Absyn.ComponentRef functionName;
  input Absyn.FunctionArgs functionArgs;
  input Component.Scope scope;
  input ComponentNode component;
  input SourceInfo info;
  output DAE.Exp typedExp;
  output DAE.Type ty;
  output DAE.Const variability;
protected
  String fn_name;
  Absyn.Path fn, fn_1;
  ComponentNode fakeComponent;
  InstNode classNode;
  list<DAE.Exp> arguments;
  DAE.CallAttributes ca;
  DAE.Type classType, resultType;
  list<DAE.FuncArg> funcArg;
  DAE.FunctionAttributes functionAttributes;
  DAE.TypeSource source;
  Prefix prefix;
  SCode.Element cls;
  list<DAE.Var> vars;
  list<Absyn.Exp> args;
  DAE.Const argVariability;
  DAE.FunctionBuiltin isBuiltin;
  Boolean builtin;
  DAE.InlineType inlineType;
algorithm
  try
    // make sure the component is a path (no subscripts)
    fn := Absyn.crefToPath(functionName);
  else
    fn_name := Dump.printComponentRefStr(functionName);
    Error.addSourceMessageAndFail(Error.SUBSCRIPTED_FUNCTION_CALL, {fn_name}, info);
    fail();
  end try;

  try
    // try to lookup the function, if is working then is either a user defined function or present in ModelicaBuiltin.mo
    (classNode, prefix) := Lookup.lookupFunctionName(functionName, scope, component, info);
  else
    // we could not lookup the class, see if is a special builtin such as String(), etc
    if isSpecialBuiltinFunctionName(functionName) then
      (typedExp, ty, variability) := typeSpecialBuiltinFunctionCall(functionName, functionArgs, scope, component, info);
      return;
    end if;
    // fail otherwise
    fail();
  end try;

  classNode := Inst.instantiate(classNode, Modifier.NOMOD(), component);
  fn_name :=  InstNode.name(classNode);
  cls := InstNode.definition(classNode);
  // create a component that has the name of the function and the scope of the function as its type
  fakeComponent := ComponentNode.new(fn_name,
     SCode.COMPONENT(
       fn_name,
       SCode.defaultPrefixes,
       SCode.defaultVarAttr,
       Absyn.TPATH(fn, NONE()),
       SCode.NOMOD(),
       SCode.COMMENT(NONE(), NONE()),
       NONE(),
       info), component);

  fakeComponent := Inst.instComponent(fakeComponent, component, InstNode.parentScope(classNode));

  // we need something better than this as this will type the function twice
  fakeComponent := NFTyping.typeComponent(fakeComponent);
  (classNode, classType) := NFTyping.typeClass(classNode, fakeComponent);

  // see if the class is a builtin function (including definitions in the ModelicaBuiltin.mo), record or normal function

  // is builtin function defined in ModelicaBuiltin.mo
  if isBuiltinFunctionName(functionName) then
    (typedExp, ty, variability) := typeBuiltinFunctionCall(functionName, functionArgs, prefix, classNode, classType, cls, scope, component, info);
    return;
  end if;

  // is record
  if SCode.isRecord(cls) then
    (typedExp, ty, variability) := NFRecord.typeRecordCall(functionName, functionArgs, prefix, classNode, classType, cls, scope, component, info);
    return;
  end if;

  // is normal function call
  (typedExp, ty, variability) := typeNormalFunction(functionName, functionArgs, prefix, classNode, classType, cls, scope, component, info);

end typeFunctionCall;

function getFunctionInputs
  input InstNode classNode;
  output list<ComponentNode> inputs = {};
protected
  ComponentNode cn;
  Component.Attributes attr;
  array<ComponentNode> components;
algorithm
  Instance.INSTANCED_CLASS(components = components) := InstNode.instance(classNode);

  for i in arrayLength(components):-1:1 loop
     cn := components[i];
     attr := Component.getAttributes(ComponentNode.component(cn));
     inputs := match attr
                 case Component.ATTRIBUTES(direction = DAE.INPUT()) then cn::inputs;
                 else inputs;
               end match;
  end for;
end getFunctionInputs;

function getFunctionOutputs
  input InstNode classNode;
  output list<ComponentNode> outputs = {};
protected
  ComponentNode cn;
  Component.Attributes attr;
  array<ComponentNode> components;
algorithm
  Instance.INSTANCED_CLASS(components = components) := InstNode.instance(classNode);

  for i in arrayLength(components):-1:1 loop
     cn := components[i];
     attr := Component.getAttributes(ComponentNode.component(cn));
     outputs := match attr
                 case Component.ATTRIBUTES(direction = DAE.OUTPUT()) then cn::outputs;
                 else outputs;
               end match;
  end for;
end getFunctionOutputs;

// TODO FIXME! how do we handle vectorization? maybe using the commented out code in NFTypeCheck.mo?
function typeNormalFunction
  input Absyn.ComponentRef functionName;
  input Absyn.FunctionArgs functionArgs;
  input Prefix prefix;
  input InstNode classNode;
  input DAE.Type classType;
  input SCode.Element cls;
  input Component.Scope scope;
  input ComponentNode component;
  input SourceInfo info;
  output DAE.Exp typedExp;
  output DAE.Type ty;
  output DAE.Const variability;
protected
  String fn_name, argName;
  Absyn.Path fn, fn_1;
  ComponentNode fakeComponent;
  Component c;
  DAE.CallAttributes ca;
  DAE.Type resultType;
  list<DAE.FuncArg> funcArg;
  DAE.FunctionAttributes functionAttributes;
  DAE.TypeSource source;
  list<DAE.Var> vars;
  Absyn.Exp arg;
  list<Absyn.Exp> args;
  list<Absyn.NamedArg> nargs;
  list<DAE.Exp> dargs, dnargs; // dae args, dae named args
  list<DAE.Type> dargstys = {}, dnargstys = {}; // dae args types, dae named args types
  list<DAE.Const> dargsvrs = {}, dnargsvrs = {}; // dae args variability, dae named args variability
  list<String> dnargsnames = {}; // the named args names
  DAE.FunctionBuiltin isBuiltin;
  Boolean builtin;
  DAE.InlineType inlineType;
  list<ComponentNode> inputs;
  list<DAE.Exp> dargs;
  DAE.Exp darg;
  DAE.Type dty;
  DAE.Const dvr;
  list<FunctionSlot> slots = {}, tslots = {};
  FunctionSlot s;
  Component.Attributes attr;
  DAE.VarKind vk;
  NFBinding.Binding b;
  Option<NFBinding.Binding> ob;
  String sname "the name of the slot";
  Option<tuple<DAE.Exp, DAE.Type, DAE.Const>> sarg "the argument given by the function call";
  Option<NFBinding.Binding> sdefault "the default value from binding of the input component in the function";
  Option<tuple<DAE.Type, DAE.Const>> sexpected "the actual type of the input component, what we expect to get";

algorithm

  fn := Absyn.crefToPath(functionName);

  Absyn.FUNCTIONARGS(args = args, argNames = nargs) := functionArgs;

  inputs := getFunctionInputs(classNode);

  // create the slots
  for i in inputs loop
    argName := ComponentNode.name(i);
    c := ComponentNode.component(i);
    attr := Component.getAttributes(c);
    Component.ATTRIBUTES(variability = vk) := attr;
    dvr := NFTyping.variabilityToConst(NFInstUtil.daeToSCodeVariability(vk));
    b := Component.getBinding(c);
    ob := match b case NFBinding.Binding.TYPED_BINDING() then SOME(b); else then NONE(); end match;
    ty := Component.getType(c);
    slots := SLOT(argName, NONE(), ob, SOME((ty, dvr)), false)::slots;
  end for;
  slots := listReverse(slots);

  // handle positional args
  for a in args loop
    (darg, dty, dvr) := NFTyping.typeExp(a, scope, component, info);
    s::slots := slots;
    // replace sarg in the slot
    SLOT(sname, sarg, sdefault, sexpected, _) := s;
    sarg := SOME((darg, dty, dvr));
    s := SLOT(sname, sarg, sdefault, sexpected, true);
    tslots := s::tslots;
  end for;
  slots := listAppend(listReverse(tslots), slots);

  // handle named args
  for n in nargs loop
    Absyn.NAMEDARG(argName = argName, argValue = arg) := n;
    (darg, dty, dvr) := NFTyping.typeExp(arg, scope, component, info);
    slots := fillNamedSlot(slots, argName, (darg, dty, dvr), fn, prefix, info);
  end for;

  // check that there are no unfilled slots and the types of actual arguments agree with the type of function arguments
  typeCheckFunctionSlots(slots, fn, prefix, info);

  (dargs, variability) := argsFromSlots(slots);

  DAE.T_COMPLEX(varLst = vars) := classType;
  functionAttributes := InstUtil.getFunctionAttributes(cls, vars);
  ty := Types.makeFunctionType(fn, vars, functionAttributes);

  DAE.T_FUNCTION(funcResultType = resultType) := ty;

  (isBuiltin,builtin,fn_1) := Static.isBuiltinFunc(fn, ty);
  inlineType := Static.inlineBuiltin(isBuiltin,functionAttributes.inline);

  ca := DAE.CALL_ATTR(
          resultType,
          Types.isTuple(resultType),
          builtin,
          functionAttributes.isImpure or (not functionAttributes.isOpenModelicaPure),
          functionAttributes.isFunctionPointer,
          inlineType,DAE.NO_TAIL());

  typedExp := DAE.CALL(fn_1, dargs, ca);

end typeNormalFunction;

function argsFromSlots
  input list<FunctionSlot> slots;
  output list<DAE.Exp> args = {};
  output DAE.Const c = DAE.C_CONST();
protected
  Integer d;
  DAE.Exp arg;
  Option<tuple<DAE.Exp, DAE.Type, DAE.Const>> sarg "the argument given by the function call";
  Option<NFBinding.Binding> sdefault "the default value from binding of the input component in the function";
  DAE.Const const;
algorithm
  for s in slots loop
    SLOT(arg = sarg, default = sdefault) := s;
    if isSome(sarg) then
      SOME((arg, _, const)) := sarg;
      c := Types.constAnd(c, const);
    else
      // TODO FIXME what do we do with the propagatedDims?
      SOME(NFBinding.TYPED_BINDING(bindingExp = arg, variability = const, propagatedDims = d)) := sdefault;
      c := Types.constAnd(c, const);
    end if;
    args := arg :: args;
  end for;
  args := listReverse(args);
end argsFromSlots;

function typeCheckFunctionSlots
  input list<FunctionSlot> slots;
  input Absyn.Path fn;
  input Prefix prefix;
  input SourceInfo info;
algorithm
protected
  String str1, str2, s1, s2, s3, s4, s5;
  Boolean b, found = false;
  String sname "the name of the slot";
  Option<tuple<DAE.Exp, DAE.Type, DAE.Const>> sarg "the argument given by the function call";
  Option<NFBinding.Binding> sdefault "the default value from binding of the input component in the function";
  Option<tuple<DAE.Type, DAE.Const>> sexpected "the actual type of the input component, what we expect to get";
  Boolean sisFilled;
  DAE.Exp expActual;
  DAE.Const vrActual, vrExpected;
  DAE.Type tyActual, tyExpected;
  Integer position = 0;
algorithm
  for s in slots loop
    position := position + 1;
    SLOT(sname, sarg, sdefault, sexpected, sisFilled) := s;

    // slot not filled and there is no default
    if not sisFilled and not isSome(sdefault) then
      Error.addSourceMessage(Error.UNFILLED_SLOT, {sname}, info);
      fail();
    end if;

    SOME((expActual, tyActual, vrActual)) := sarg;
    SOME((tyExpected, vrExpected)) := sexpected;

    // check the typing
    try
      _ := Types.matchType(expActual, tyActual, tyExpected, true);
    else
      s1 := intString(position);
      s2 := Absyn.pathStringNoQual(fn);
      s3 := ExpressionDump.printExpStr(expActual);
      s4 := Types.unparseTypeNoAttr(tyActual);
      s5 := Types.unparseTypeNoAttr(tyExpected);
      Error.addSourceMessage(Error.ARG_TYPE_MISMATCH, {s1,s2,sname,s3,s4,s5}, info);
      fail();
    end try;

    // fail if the variability is wrong
    if not Types.constEqualOrHigher(vrActual, vrExpected) then
      str1 := ExpressionDump.printExpStr(expActual);
      str2 := DAEUtil.constStrFriendly(vrExpected);
      Error.addSourceMessageAndFail(Error.FUNCTION_SLOT_VARIABILITY, {sname, str1, str2}, info);
    end if;
  end for;
end typeCheckFunctionSlots;

function fillNamedSlot
  input list<FunctionSlot> islots;
  input String name;
  input tuple<DAE.Exp, DAE.Type, DAE.Const> arg;
  input Absyn.Path fn;
  input Prefix prefix;
  input SourceInfo info;
  output list<FunctionSlot> oslots = {};
protected
  String str;
  Boolean b, found = false;
  String sname "the name of the slot";
  Option<tuple<DAE.Exp, DAE.Type, DAE.Const>> sarg "the argument given by the function call";
  Option<NFBinding.Binding> sdefault "the default value from binding of the input component in the function";
  Option<tuple<DAE.Type, DAE.Const>> sexpected "the actual type of the input component, what we expect to get";
  Boolean sisFilled;
algorithm
  for s in islots loop
    SLOT(sname, sarg, sdefault, sexpected, sisFilled) := s;
    if (name == sname) then
      found := true;
      // if the slot is already filled, Huston we have a problem, add an error
      if sisFilled then
        str := Prefix.toString(prefix) + "." + Absyn.pathString(fn);
        Error.addSourceMessageAndFail(Error.FUNCTION_SLOT_ALLREADY_FILLED, {name, str}, info);
      end if;
      oslots := SLOT(sname, SOME(arg), sdefault, sexpected, true) :: oslots;
    else
      oslots := s :: oslots;
    end if;
  end for;
  if not found then
    str := Prefix.toString(prefix) + "." + Absyn.pathString(fn);
    Error.addSourceMessageAndFail(Error.NO_SUCH_ARGUMENT, {str, name}, info);
  end if;
end fillNamedSlot;

protected function isSpecialBuiltinFunctionName
"@author: adrpo petfr
 check if the name is special builtin function or
 operator which does not have a definition in ModelicaBuiltin.mo
 TODO FIXME, add all of them"
  input Absyn.ComponentRef functionName;
  output Boolean isBuiltinFname;
algorithm
  isBuiltinFname := matchcontinue(functionName)
    local
      String name;
      Boolean b, b1, b2;
      Absyn.ComponentRef fname;

    case (Absyn.CREF_FULLYQUALIFIED(fname))
      then
        isSpecialBuiltinFunctionName(fname);

    case (Absyn.CREF_IDENT(name, {}))
      equation
        b1 = listMember(name, {"String", "Integer"});
        // these are the new Modelica 3.3 synch operators
        b2 = if intGe(Flags.getConfigEnum(Flags.LANGUAGE_STANDARD), 33)
              then
                listMember(name, {"Clock", "previous", "hold", "subSample", "superSample", "shiftSample",
                                  "backSample", "noClock", "transition", "initialState", "activeState",
                                  "ticksInState", "timeInState"})
              else false;
        b = boolOr(b1, b2);
      then
        b;

    case (_) then false;
  end matchcontinue;
end isSpecialBuiltinFunctionName;


protected function isBuiltinFunctionName
"@author: adrpo  petfr
 check if the name is a builtin function or operator
 TODO FIXME, add all of them"
  input Absyn.ComponentRef functionName;
  output Boolean isBuiltinFname;
algorithm
  isBuiltinFname := matchcontinue(functionName)
    local
      String name;
      Boolean b;
      Absyn.ComponentRef fname;

    case (Absyn.CREF_FULLYQUALIFIED(fname))
      then
        isBuiltinFunctionName(fname);

    case (Absyn.CREF_IDENT(name, {}))
      equation

//   /*
   // Replaced the linear search listMember below by a match on
   // name vs constrant strings
   // which enables OMC to compile match to a perfect hash with direct jump
   // instead of linear search

       // See more complete list below from Static.elabbuiltinhandler.
        b = listMember(name,
          {
            "der",
            "noEvent",
            "smooth",
            "sample",
            "pre",
            "edge",
            "change",
            "reinit",
            "size",
            "rooted",
            "transpose",
            "skew",
            "identity",
            "min",
            "max",
            "cross",
            "diagonal",
            "abs",
            "sum",
            "product",
            "assert",
            "array",
            "cat",
            "rem",
            "actualStream",
            "inStream"});
      then
        b;
//     */

/*
   // The more complete list of names below is from Static.elabbuiltinhandler

    b = match (name)
    case "delay" then true;
    case "smooth" then true;
    case "size" then true;
    case "ndims" then true;
    case "zeros" then true;
    case "ones" then true;
    case "fill" then true;
    case "max" then true;
    case "min" then true;
    case "transpose" then true;
    case "symmetric" then true;
    case "array" then true;
    case "sum" then true;
    case "product" then true;
    case "pre" then true;
    case "firstTick" then true;  // ?petfr   firstTick not present in MLS 3.3 rev1
    case "interval" then true;
    case "boolean" then true;
    case "diagonal" then true;
    case "noEvent" then true;
    case "edge" then true;
    case "der" then true;
    case "change" then true;
    case "cat" then true;
    case "identity" then true;
    case "vector" then true;
    case "matrix" then true;
    case "scalar" then true;
    case "String" then true;
    case "rooted" then true;
    case "Integer" then true;
    case "EnumToInteger" then true;   // ?petfr  EnumToInteger not present in MLS 3.3 rev1
    case "inStream" then true;
    case "actualStream" then true;
    case "getInstanceName" then true;
    case "classDirectory" then true;   // ?petfr classDirectory not present in MLS 3.3 rev1
    case "sample" then true;
    case "cardinality" then true;
    case "homotopy" then true;
    case "DynamicSelect" then true;
    case "Clock" then intGe(Flags.getConfigEnum(Flags.LANGUAGE_STANDARD), 33);
    case "previous" then intGe(Flags.getConfigEnum(Flags.LANGUAGE_STANDARD), 33);
    case "hold" then intGe(Flags.getConfigEnum(Flags.LANGUAGE_STANDARD), 33);
    case "subSample" then intGe(Flags.getConfigEnum(Flags.LANGUAGE_STANDARD), 33);
    case "superSample" then intGe(Flags.getConfigEnum(Flags.LANGUAGE_STANDARD), 33);
    case "shiftSample" then intGe(Flags.getConfigEnum(Flags.LANGUAGE_STANDARD), 33);
    case "backSample" then intGe(Flags.getConfigEnum(Flags.LANGUAGE_STANDARD), 33);
    case "noClock" then intGe(Flags.getConfigEnum(Flags.LANGUAGE_STANDARD), 33);
    case "transition" then intGe(Flags.getConfigEnum(Flags.LANGUAGE_STANDARD), 33);
    case "initialState" then intGe(Flags.getConfigEnum(Flags.LANGUAGE_STANDARD), 33);
    case "activeState" then intGe(Flags.getConfigEnum(Flags.LANGUAGE_STANDARD), 33);
    case "ticksInState" then intGe(Flags.getConfigEnum(Flags.LANGUAGE_STANDARD), 33);
    case "timeInState" then intGe(Flags.getConfigEnum(Flags.LANGUAGE_STANDARD), 33);
    case "sourceInfo" then Config.acceptMetaModelicaGrammar();
    case "SOME" then Config.acceptMetaModelicaGrammar();
    case "NONE"  then Config.acceptMetaModelicaGrammar();
    case "isPresent" then Config.acceptMetaModelicaGrammar();
    else false;
    end match;

   then
       b;
*/

    case (_) then false;
  end matchcontinue;
end isBuiltinFunctionName;





// adrpo:
// - see Static.mo for how to check the input arguments or any other checks we need that should be ported
// - try to use Expression.makePureBuiltinCall everywhere instead of creating the typedExp via DAE.CALL
// - this function should handle special builtin operators which are not defined in ModelicaBuiltin.mo
protected function typeSpecialBuiltinFunctionCall
"@author: adrpo petfr
 handle all builtin calls that are not defined at all in ModelicaBuiltin.mo
 TODO FIXME, add all"
  input Absyn.ComponentRef functionName;
  input Absyn.FunctionArgs functionArgs;
  input Component.Scope scope;
  input ComponentNode component;
  input SourceInfo info;
  output DAE.Exp typedExp;
  output DAE.Type ty;
  output DAE.Const variability;
protected
   DAE.Const vr, vr1, vr2;
algorithm
  (typedExp, ty, variability) := matchcontinue(functionName, functionArgs)
    local
      Absyn.ComponentRef acref;
      Absyn.Exp aexp1, aexp2;
      DAE.Exp dexp1, dexp2;
      list<Absyn.Exp>  afargs;
      list<Absyn.NamedArg> anamed_args;
      Absyn.Path call_path;
      list<DAE.Exp> pos_args, args;
      list<tuple<String, DAE.Exp>> named_args;
      list<ComponentNode> inputs, outputs;
      Absyn.ForIterators iters;
      DAE.Dimensions d1, d2;
      DAE.TypeSource src1, src2;
      DAE.Type el_ty;
      list<DAE.Type> tys;
      list<DAE.Const> vrs;

    // TODO FIXME: String might be overloaded, we need to handle this better! See Static.mo
    case (Absyn.CREF_IDENT(name = "String"), Absyn.FUNCTIONARGS(args = afargs))
      algorithm
        call_path := Absyn.crefToPath(functionName);
        (args, tys, vrs) := NFTyping.typeExps(afargs, scope, component, info);
        vr := List.fold(vrs, Types.constAnd, DAE.C_CONST());
        ty := DAE.T_STRING_DEFAULT;
      then
        (DAE.CALL(call_path, args, DAE.callAttrBuiltinOther), ty, vr);

    // TODO FIXME: check that the input is an enumeration
    case (Absyn.CREF_IDENT(name = "Integer"), Absyn.FUNCTIONARGS(args = afargs))
      algorithm
        call_path := Absyn.crefToPath(functionName);
        (args, tys, vrs) := NFTyping.typeExps(afargs, scope, component, info);
        vr := List.fold(vrs, Types.constAnd, DAE.C_CONST());
        ty := DAE.T_INTEGER_DEFAULT;
      then
        (DAE.CALL(call_path, args, DAE.callAttrBuiltinOther), ty, vr);

    // TODO FIXME! handle all the Modelica 3.3 operators here, see isSpecialBuiltinFunctionName

 end matchcontinue;
end typeSpecialBuiltinFunctionCall;




// adrpo:
//
// - petfr: ??slow with a lot of linear search for all the builtin function names, happens for all
//  function calls in models
// - petfr: According to Martin, if we do a match only on the string value, it will do a perfect
// - hash and avoid the linear search
//
// - see Static.mo for how to check the input arguments or any other checks we need that should be ported
// - try to use Expression.makePureBuiltinCall everywhere instead of creating the typedExp via DAE.CALL
// - all the fuctions that are defined *with no input/output type* in ModelicaBuiltin.mo such as:
//     function NAME "Transpose a matrix"
//       external "builtin";
//     end NAME;
//   need to be handled here!
// - the functions which have a type in the ModelicaBuiltin.mo should be handled by the last case in this function

// - petfr: ?? how to handle vectorization?  Does vectorization apply for the builtin operators
//   even when they are mentioned as having scalar arguments?
//   petfr:  probably yes, e.g. der(arr), pre(arr)
//  Functions with one scalar return value can be applied to arrays element-wise,
//   -- if vectorization applies, should not check just for scalar types, also for arrays of scalars?
//
// - petfr: ?? What about checking for wrong # of arguments to the builtin functions? Such cases
// are not caught by the matchcontinue below. It will fall down to the general case.
// Perhaps first have a match only for the builtin function name, in each case
// followed by a nested match to take
// care of the different # of argument cases.  Also more efficient, avoids linear search.

protected function typeBuiltinFunctionCall
"@author: adrpo, petfr
 handle all builtin calls that are not in ModelicaBuiltin.mo
 TODO FIXME, add all"
  input Absyn.ComponentRef functionName;
  input Absyn.FunctionArgs functionArgs;
  input Prefix prefix;
  input InstNode classNode;
  input DAE.Type classType;
  input SCode.Element cls;
  input Component.Scope scope;
  input ComponentNode component;
  input SourceInfo info;
  output DAE.Exp typedExp;
  output DAE.Type ty;
  output DAE.Const variability;
protected
   String fnName;
   DAE.Const vr, vr1, vr2;
algorithm
  (typedExp, ty, variability) := matchcontinue (functionName, functionArgs)
    local
      Absyn.ComponentRef acref;
      Absyn.Exp aexp1, aexp2;
      DAE.Exp dexp1, dexp2;
      list<Absyn.Exp>  afargs;
      list<Absyn.NamedArg> anamed_args;
      Absyn.Path call_path;
      list<DAE.Exp> pos_args, args;
      list<tuple<String, DAE.Exp>> named_args;
      list<ComponentNode> inputs, outputs;
      Absyn.ForIterators iters;
      DAE.Dimension d1, d2;
      DAE.Dimensions dimsOfArr;
      Integer dim_int, dim_count;
      DAE.TypeSource src1, src2;
      DAE.Type el_ty, ty1, ty2;

    // size(arr, i) returns the size of dimension i of array expression arr
    // where i shall be > 0 and <= ndims(arr)
    // Here only type and variability of size()
    case (Absyn.CREF_IDENT(name = "size"), Absyn.FUNCTIONARGS(args = {aexp1, aexp2}))
      algorithm
        (dexp1, ty1, vr1) := NFTyping.typeExp(aexp1, scope, component, info); // arr
        (dexp2, ty2, vr2) := NFTyping.typeExp(aexp2, scope, component, info); // dim index i

        DAE.T_ARRAY(dims = dimsOfArr) := ty1;
        dim_count := listLength(dimsOfArr);

        if dim_count == 0 then
          // zero dimensions, size of a scalar is not allowed.
          errorFailBuiltinSpecError(functionName, functionArgs, Error.INVALID_ARGUMENT_TYPE_FIRST_ARRAY, "", info);
        end if;

        // the size variability does not actually depend on the variability of "arr" but on the variability
        // of the particular dimension of "arr"
        try
          dim_int := Expression.expInt(dexp2);
          // size(A, i) for an array A with known dimensions and constant i.
          if (dim_int <= 0 or dim_int > dim_count) then
            // dim index out of bounds
            errorFailBuiltinSpecError(functionName, functionArgs,
              Error.INVALID_SIZE_INDEX, intString(dim_int), info);
          end if;
          d1 := listGet(dimsOfArr, dim_int);
          _ := Expression.dimensionSizeConstantExp(d1);  // Check if dimension is constant
          vr := DAE.C_CONST();
        else
          // size(A, i) for an array A with unknown dimensions or non-constant i.
          vr := DAE.C_PARAM();
        end try;

        // TODO FIXME: calculate the correct type and the correct variability, see Static.elabBuiltinSize in Static.mo  ??petfr fixed. check!
        ty := DAE.T_INTEGER_DEFAULT;

      then
        (DAE.SIZE(dexp1, SOME(dexp2)), ty, vr);


    // size(arr)
    // Operator returns a vector of length ndims(arr) containing the dimension sizes of arr.
    // Here only type and variability of size()
    case (Absyn.CREF_IDENT(name = "size"), Absyn.FUNCTIONARGS(args = {aexp1}))
      algorithm
        (dexp1, ty1, vr1) := NFTyping.typeExp(aexp1, scope, component, info);
        // TODO FIXME: calculate the correct type and the correct variability,  ??petfr fixed, check!
        // see Static.elabBuiltinSize in Static.mo
        ty := DAE.T_INTEGER_DEFAULT;

        DAE.T_ARRAY(dims = dimsOfArr) := ty1;

        _ := match dimsOfArr
          // zero dimensions, size of a scalar is not allowed.
          case {}  equation
            errorFailBuiltinSpecError(functionName, functionArgs,
              Error.INVALID_ARGUMENT_TYPE_FIRST_ARRAY, "", info);
            then ();
          else
            ();
        end match;

        // the variability of size does not actually depend on the variability of "arr" but on the
        // variability of the dimensions of "arr"
        try
          _ := List.map(dimsOfArr, Expression.dimensionSizeExp); // fails if one dim size is unknown
          // size(A) for an array A with known dimension sizes.  Variability is constant
          vr := DAE.C_CONST();
        else
          // size(A) for an array A with at least one unknown dimension.  variability is param
          vr := DAE.C_PARAM();
        end try;

      then
        (DAE.SIZE(dexp1, NONE()), ty, vr);


    // smooth(p, expr)
    // smooth(p,expr) - If p>=0 smooth(p, expr) returns expr and states that expr is p times
    // continuously differentiable, i.e.: expr is continuous in all real variables appearing in
    // the expression and all partial derivatives with respect to all appearing real variables
    // exist and are continuous up to order p.
    // The only allowed types for expr in smooth are: real expressions, arrays of
    // allowed expressions, and records containing only components of allowed expressions."
    case (Absyn.CREF_IDENT(name = "smooth"), Absyn.FUNCTIONARGS(args = {aexp1, aexp2}))
      algorithm
        call_path := Absyn.crefToPath(functionName);
        (dexp1, ty1, vr1) := NFTyping.typeExp(aexp1, scope, component, info);
        (dexp2, ty2, vr2) := NFTyping.typeExp(aexp1, scope, component, info);

        if not Types.isParameterOrConstant(vr1) or not Types.isInteger(ty1) then
          errorFailBuiltinWrongArgTypes(functionName, functionArgs,
            "first argument must be a constant or parameter expression of type Integer", info);
        end if;
        if not (Types.isReal(ty2) or Types.isRecordWithOnlyReals(ty2)) then
          errorFailBuiltinWrongArgTypes(functionName, functionArgs,
            "second argument must be a Real, array of Reals or record only containing Reals", info);
        end if;

        // TODO FIXME: calculate the correct type and the correct variability, see Static.mo
        ty := Types.simplifyType(ty2);  //  from static ??OK?, why need simplifyType?
        vr := vr2;
      then
        (DAE.CALL(call_path, {dexp1,dexp2}, DAE.callAttrBuiltinOther), ty, vr);

  /* ?? Generally TODO Need to add checks for # arguments for all operators later  -- remove this comment
    e.g. from Static:  if listLength(inPosArgs) <> 2 or not listEmpty(inNamedArgs) then
       msg_str := ", expected smooth(p, expr)";
       printBuiltinFnArgError("smooth", msg_str, inPosArgs, inNamedArgs, inPrefix, inInfo);
     end if;
  */


    // Connections.rooted(A.R) returns true, if A.R is closer to the root of the spanning tree than B.R;
    // otherwise false is returned.  NOTE: rooted(A.R);  is deprecated (but still used?)
    // R is an overdetermined type or record instance in connector instance A

 // ?? from Static, where? to check "Connections.rooted" instead of just "rooted"
 //     case Absyn.CREF_QUAL(name = "Connections", componentRef = Absyn.CREF_IDENT(name = "rooted"))
 //     then elabBuiltinRooted(inCache, inEnv, inPosArgs, inNamedArgs, inImplicit, inPrefix, inInfo);
//    case Absyn.CREF_FULLYQUALIFIED(cr)
//      then elabCallBuiltin(inCache, inEnv, cr, inPosArgs, inNamedArgs, inImplicit, inPrefix, inInfo);
//  checkBuiltinCallArgs(inPosArgs, inNamedArgs, 1, "Connections.isRoot", inInfo);
// ...
//  outExp := DAE.CALL(Absyn.QUALIFIED("Connections", Absyn.IDENT("isRoot")),

    case (Absyn.CREF_IDENT(name = "rooted"), Absyn.FUNCTIONARGS(args = {aexp1}))
      algorithm
        call_path := Absyn.crefToPath(functionName);
        (dexp1, ty1, vr1) := NFTyping.typeExp(aexp1, scope, component, info);

        // TODO FIXME: calculate the correct type and the correct variability, see Static.mo -- fixed
        ty := DAE.T_BOOL_DEFAULT;
        vr := DAE.C_VAR();     // ?? this OK variability?  from Static - remove this comment
        _ := match dexp1
          case DAE.ARRAY(array = {})  // ??OK ? Added this check for size zero since checked in Static
            equation
              Error.addSourceMessage(Error.OVERCONSTRAINED_OPERATOR_SIZE_ZERO_RETURN_FALSE,
                { Dump.printComponentRefStr(functionName) }, info);
              fail();
            then ();
          else ();
        end match;

      then
        (DAE.CALL(call_path, {dexp1}, DAE.callAttrBuiltinOther), ty, vr);


 // ?? from Static:  checking # arguments
 //  checkBuiltinCallArgs(inPosArgs, inNamedArgs, 1, "Connections.isRoot", inInfo);
 /*
protected function checkBuiltinCallArgs
  input list<Absyn.Exp> inPosArgs;
  input list<Absyn.NamedArg> inNamedArgs;
  input Integer inExpectedArgs;
  input String inFnName;
  input Absyn.Info inInfo;
protected
  String args_str, msg_str;
  list<String> pos_args, named_args;
algorithm
  if listLength(inPosArgs) <> inExpectedArgs or not listEmpty(inNamedArgs) then
    Error.addSourceMessageAndFail(Error.WRONG_NO_OF_ARGS, {inFnName}, inInfo);
  end if;
end checkBuiltinCallArgs;
*/


    case (Absyn.CREF_IDENT(name = "transpose"), Absyn.FUNCTIONARGS(args = {aexp1}))
      algorithm
        (dexp1, ty1, vr1) := NFTyping.typeExp(aexp1, scope, component, info);
        try
          true := Types.isArray(ty1);
          DAE.T_ARRAY(DAE.T_ARRAY(el_ty, {d1}, src1), {d2}, src2) := ty1;
        else
          errorFailBuiltinWrongArgTypes(functionName, functionArgs,
            "Two-dimensional array expected", info);
        end try;

        // transpose the type.
        ty := DAE.T_ARRAY(DAE.T_ARRAY(el_ty, {d2}, src1), {d1}, src2);

        // create the typed transpose expression
        typedExp := Expression.makePureBuiltinCall("transpose", {dexp1}, ty);
        vr := vr1;
      then
        (typedExp, ty, vr);

    // min(arr)  made min and max into separate cases, to avoid every function matching into those cases

    // min(arr) Returns the least element of array expression arr as a scalar
    // Element type: Scalar enumeration, Boolean, Integer or Real
    case (Absyn.CREF_IDENT(name = "min"), Absyn.FUNCTIONARGS(args = {aexp1}))
      algorithm
        (dexp1, ty1, vr1) := NFTyping.typeExp(aexp1, scope, component, info);
        try
          true := Types.isArray(ty1);
          el_ty := Types.arrayElementType(ty1);
          true := Types.isSimpleTypeRealOrIntegerOrBooleanOrEnumOrSubtypes(el_ty);
        else
          errorFailBuiltinWrongArgTypes(functionName, functionArgs,
            "Integer, Real, Boolean or Enumeration array argument expected", info);
        end try;
        dexp1 := Expression.matrixToArray(dexp1);  // ??who convert from DAE.Matrix to DAE.Array?
                                         // ?? Why DAE.Array here and DAE.T_ARRAY in transpose?
                                         // DAE.T_ARRAY - arrays of unknown size, e.g. Real[:]
        ty := el_ty;
        vr := vr1;
        typedExp := Expression.makePureBuiltinCall("min", {dexp1}, ty);
      then
        (typedExp, ty, vr);

   // max(arr) Returns the greatest element of array expression arr
   // Element type: Scalar enumeration, Boolean, Integer or Real
    case (Absyn.CREF_IDENT(name = "max"), Absyn.FUNCTIONARGS(args = {aexp1}))
      algorithm
        (dexp1, ty1, vr1) := NFTyping.typeExp(aexp1, scope, component, info); // ??petfr working
        try
          true := Types.isArray(ty1);
          el_ty := Types.arrayElementType(ty1);
          true := Types.isSimpleTypeRealOrIntegerOrBooleanOrEnumOrSubtypes(el_ty);
        else
          errorFailBuiltinWrongArgTypes(functionName, functionArgs,
            "Integer, Real, Boolean or Enumeration array argument expected", info);
        end try;
        dexp1 := Expression.matrixToArray(dexp1);  // ?? why is this call needed, a matrix is an array.
                                                   // Lowering? Changes from DAE.Matrix to DAE.Array
                                                   // DAE.ARRAY - Array constructor, e.g. {1,3,4}
        ty := el_ty;
        vr := vr1;
        typedExp := Expression.makePureBuiltinCall("max", {dexp1}, ty);
      then
        (typedExp, ty, vr);


    // min(x,y) where x & y are scalars.
    // Made min and max into separate cases, to avoid most functions partially matching this
    // If vectorized, x and y are arrays. Now assumes always scalar according to MLS
    case (Absyn.CREF_IDENT(name = "min"), Absyn.FUNCTIONARGS(args = {aexp1, aexp2}))
      algorithm
        (dexp1, ty1, vr1) := NFTyping.typeExp(aexp1, scope, component, info);
        (dexp2, ty2, vr2) := NFTyping.typeExp(aexp2, scope, component, info);
        try
          true := Types.isSimpleTypeRealOrIntegerOrBooleanOrEnumOrSubtypes(ty1);
          true := Types.isSimpleTypeRealOrIntegerOrBooleanOrEnumOrSubtypes(ty2);
        else
          errorFailBuiltinWrongArgTypes(functionName, functionArgs,
            "Integer, Real, Boolean or Enumeration arguments expected", info);
        end try;
        ty := Types.scalarSuperType(ty1, ty2);
        (dexp1, _) := Types.matchType(dexp1, ty1, ty, true);
        (dexp2, _) := Types.matchType(dexp2, ty2, ty, true);
        vr := Types.constAnd(vr1, vr2);
        typedExp := Expression.makePureBuiltinCall("min", {dexp1, dexp2}, ty);
      then
        (typedExp, ty, vr);

    // max(x,y) where x & y are scalars: Integer, Real, Boolean or Enumeration or subtypes of those
    // If vectorized, x and y are arrays. Now assumes always scalar according to MLS
    case (Absyn.CREF_IDENT(name = "max"), Absyn.FUNCTIONARGS(args = {aexp1, aexp2}))
      algorithm
        (dexp1, ty1, vr1) := NFTyping.typeExp(aexp1, scope, component, info);
        (dexp2, ty2, vr2) := NFTyping.typeExp(aexp2, scope, component, info);
        try
          true := Types.isSimpleTypeRealOrIntegerOrBooleanOrEnumOrSubtypes(ty1);
          true := Types.isSimpleTypeRealOrIntegerOrBooleanOrEnumOrSubtypes(ty2);
        else
          errorFailBuiltinWrongArgTypes(functionName, functionArgs,
            "Integer, Real, Boolean or Enumeration arguments expected", info);
        end try;
        ty := Types.scalarSuperType(ty1, ty2);
        (dexp1, _) := Types.matchType(dexp1, ty1, ty, true);
        (dexp2, _) := Types.matchType(dexp2, ty2, ty, true);
        vr := Types.constAnd(vr1, vr2);
        typedExp := Expression.makePureBuiltinCall("max", {dexp1, dexp2}, ty);
      then
        (typedExp, ty, vr);

     // diagonal(v)  Returns a square matrix with the elements of vector v on the diagonal
     // and all other elements zero
    case (Absyn.CREF_IDENT(name = "diagonal"), Absyn.FUNCTIONARGS(args = {aexp1}))
      algorithm
        (dexp1, ty1, vr1) := NFTyping.typeExp(aexp1, scope, component, info);
        DAE.T_ARRAY(dims = {d1}, ty = el_ty) := ty1;

        ty := DAE.T_ARRAY(DAE.T_ARRAY(el_ty, {d1}, DAE.emptyTypeSource), {d1}, DAE.emptyTypeSource);
        typedExp := Expression.makePureBuiltinCall("diagonal", {dexp1}, ty);
        vr := vr1;
      then
        (typedExp, ty, vr);

     // product(A) returns scalar product of all the elements of array expression A
     // This means that the result type is a scalar type, not an array type
     // Element types can be Integer or Real
 /**/   case (Absyn.CREF_IDENT(name = "product"), Absyn.FUNCTIONARGS(args = {aexp1}))
      algorithm
        (dexp1, ty1, vr1) := NFTyping.typeExp(aexp1, scope, component, info);
        try
          true := Types.isArray(ty1);
          // Here, we extract the element type of array type
          ty := Types.arrayElementType(ty1);
          true := Types.isSimpleNumericType(ty);
        else
          errorFailBuiltinWrongArgTypes(functionName, functionArgs,
            "Integer or Real array argument expected", info);
        end try;
        typedExp :=  Expression.makePureBuiltinCall("product", {dexp1}, ty);
        vr := vr1;
      then
        (typedExp, ty, vr);

       // pre(y) returns left limit y(tpre) of variable y(t) at a time instant t
       // pre() operator can be applied if the following three conditions are fulfilled simultaneously:
       // (a) variable y is either a subtype of a simple type or is a record component,
       // What is Simple type? MLS 3.7.3.1 talks about Real, Integer, Boolean or enum
       // (b) y is a discrete-time expression
       // (c) the operator is not applied in a function class  ?? where is this checked?
       // y is an array if vectorized
/**/ case (Absyn.CREF_IDENT(name = "pre"), Absyn.FUNCTIONARGS(args = {aexp1}))
      algorithm
        (dexp1, ty1, vr1) := NFTyping.typeExp(aexp1, scope, component, info);
        typedExp :=  Expression.makePureBuiltinCall("pre", {dexp1}, ty1);
        try
          true := Types.isTypeRealOrIntegerOrBooleanOrEnumOrSubtypes(ty1); //?? Does not yet allow record
            // ?? If record added, should probably be records of Real, Int, Bool, Enum components
        else
          errorFailBuiltinWrongArgTypes(functionName, functionArgs,
            "Integer, Real, Boolean, or enumeration argument expected", info);
        end try;
        // ?? should also check discrete variability if not in a when-clause, and not appl in a function
      then
        (typedExp, ty1, vr1);

      // noEvent(expr)  Real elementary relations within expr are taken literally,
      // i.e., no state or time event is triggered
/**/   case (Absyn.CREF_IDENT(name = "noEvent"), Absyn.FUNCTIONARGS(args = {aexp1}))
      algorithm
        (dexp1, ty1, vr1) := NFTyping.typeExp(aexp1, scope, component, info);
        typedExp :=  Expression.makePureBuiltinCall("noEvent", {dexp1}, ty1);
      then
        (typedExp, ty1, vr1);

/**/   // sum(A) Returns the scalar sum of all the elements of array expression
       // The type of sum is the same as the element type, must be scalar Integer or Real
    case (Absyn.CREF_IDENT(name = "sum"), Absyn.FUNCTIONARGS(args = {aexp1}))
      algorithm
       (dexp1, ty1, vr1) := NFTyping.typeExp(aexp1, scope, component, info);
        ty := Types.arrayElementType(ty1);
        typedExp :=  Expression.makePureBuiltinCall("sum", {dexp1}, ty);
      then
       (typedExp, ty, vr1);

  /* assert is not a function, should not be here */
  // inst_assert, inst.assert should not be here
  // Example:  assert(size(a,1)==size(a,2),"Matrix must be square");
  //   assert(condition, message); // Uses level=AssertionLevel.error
  //   assert(condition, message, assertionLevel);
  //   assert(condition, message, level = assertionLevel);
  //  First argument is Boolean, second is a string, third is an Integer.  COuld be declared?
  //  ?? an assert statement has no type, or we just ignore it?  Is there a void type?  AnyType?



      // edge(b) is expanded into (b and not pre(b)) for Boolean variable b
      // The same restrictions as for pre() apply, e.g. not to be used inside functions.
      // if vectorized, b can be a Boolean array
      // ?? should also check for discrete variability if not in a when-clause
 /**/  case (Absyn.CREF_IDENT(name = "edge"), Absyn.FUNCTIONARGS(args = {aexp1}))
      algorithm
        (dexp1, ty1, vr1) := NFTyping.typeExp(aexp1, scope, component, info);
        typedExp :=  Expression.makePureBuiltinCall("edge", {dexp1}, ty1);
        ty := DAE.T_BOOL_DEFAULT;
        try
          true := Types.isBoolean(ty1);
        else
          errorFailBuiltinWrongArgTypes(functionName, functionArgs,
            "Boolean argument expected", info);
        end try;
      then
        (typedExp, ty, vr1);

      // change(v) is expanded into  (v<>pre(v)).
      // The same restrictions as for the pre() operator apply.
      // If vectorized, v is an array
 /**/  case (Absyn.CREF_IDENT(name = "change"), Absyn.FUNCTIONARGS(args = {aexp1}))
      algorithm
        (dexp1, ty1, vr1) := NFTyping.typeExp(aexp1, scope, component, info);
        typedExp :=  Expression.makePureBuiltinCall("change", {dexp1}, ty1);
        ty := DAE.T_BOOL_DEFAULT;
        try
          true := Types.isTypeRealOrIntegerOrBooleanOrEnumOrSubtypes(ty1); //?? Does not yet allow record
            // ?? If record added, should probably be records of Real, Int, Bool, Enum components
        else
          errorFailBuiltinWrongArgTypes(functionName, functionArgs,
            "Integer, Real, Boolean, or enumeration argument expected", info);
        end try;

        // ?? should also check discrete variability if not in a when-clause, and not used in a function
      then
        (typedExp, ty, vr1);

/**/ // rem(x,y)  Returns the integer remainder of x/y, such that div(x,y)*y + rem(x, y) = x.
     //  Result and arguments shall have type Real or Integer.
     //  If either of the arguments is Real the result is Real otherwise Integer.
     //  If vectorized, x and y are arrays
     //  ?? Checking vectorization also implies checking that both arguments have the same dimensions
    case (Absyn.CREF_IDENT(name = "rem"), Absyn.FUNCTIONARGS(args = {aexp1, aexp2}))
      algorithm
        (dexp1, ty1, vr1) := NFTyping.typeExp(aexp1, scope, component, info);
        (dexp2, ty2, vr2) := NFTyping.typeExp(aexp2, scope, component, info);
        try
          true := Types.isNumericType(ty1);
          true := Types.isNumericType(ty2);
        else
          errorFailBuiltinWrongArgTypes(functionName, functionArgs,
            "Integer or Real arguments expected", info);
        end try;
        ty := Types.scalarSuperType(ty1, ty2);  // Integer & Integer -> Integer otherwise Real
        (dexp1, _) := Types.matchType(dexp1, ty1, ty, true); // Conv Integer to Real if needed
        (dexp2, _) := Types.matchType(dexp2, ty2, ty, true); // Conv Integer to Real if needed
        vr := Types.constAnd(vr1, vr2);  // Variability of result

        typedExp := Expression.makePureBuiltinCall("rem", {dexp1, dexp2}, ty);
      then
        (typedExp, ty, vr);

/**/ // div(x,y)  Returns the algebraic quotient x/y with any fractional part discarded
     //   Result and arguments shall have type Real or Integer. (or subtypes of those)
     //   If either of the arguments is Real the result is Real otherwise Integer
     //  If vectorized, x and y are arrays
     //  ?? Checking vectorization also implies checking that both arguments have the same dimensions
    case (Absyn.CREF_IDENT(name = "div"), Absyn.FUNCTIONARGS(args = {aexp1, aexp2}))
      algorithm
        (dexp1, ty1, vr1) := NFTyping.typeExp(aexp1, scope, component, info);
        (dexp2, ty2, vr2) := NFTyping.typeExp(aexp2, scope, component, info);
        try
          true := Types.isNumericType(ty1);
          true := Types.isNumericType(ty2);
        else
          errorFailBuiltinWrongArgTypes(functionName, functionArgs,
            "Integer or Real arguments expected", info);
        end try;
        ty := Types.scalarSuperType(ty1, ty2);  // Integer & Integer -> Integer otherwise Real
        (dexp1, _) := Types.matchType(dexp1, ty1, ty, true); // Conv Integer to Real if needed
        (dexp2, _) := Types.matchType(dexp2, ty2, ty, true); // Conv Integer to Real if needed
        vr := Types.constAnd(vr1, vr2);  // Variability of result

        typedExp := Expression.makePureBuiltinCall("div", {dexp1, dexp2}, ty);
      then
        (typedExp, ty, vr);


 /**/ // mod(x,y)  Returns the integer modulus of x/y, i.e. mod(x,y)=x-floor(x/y)*y
     //  Result and arguments shall have type Real or Integer. (or subtypes of those)
     //  If either of the arguments is Real the result is Real otherwise Integer
     //  If vectorized, x and y are arrays
     //  ?? Checking vectorization also implies checking that both arguments have the same dimensions
    case (Absyn.CREF_IDENT(name = "mod"), Absyn.FUNCTIONARGS(args = {aexp1, aexp2}))
      algorithm
        (dexp1, ty1, vr1) := NFTyping.typeExp(aexp1, scope, component, info);
        (dexp2, ty2, vr2) := NFTyping.typeExp(aexp2, scope, component, info);
        try
          true := Types.isNumericType(ty1);
          true := Types.isNumericType(ty2);
        else
          errorFailBuiltinWrongArgTypes(functionName, functionArgs,
            "Integer or Real arguments expected", info);
        end try;
        ty := Types.scalarSuperType(ty1, ty2);  // Integer & Integer -> Integer otherwise Real
        (dexp1, _) := Types.matchType(dexp1, ty1, ty, true); // Conv Integer to Real if needed
        (dexp2, _) := Types.matchType(dexp2, ty2, ty, true); // Conv Integer to Real if needed
        vr := Types.constAnd(vr1, vr2);  // Variability of result

        typedExp := Expression.makePureBuiltinCall("mod", {dexp1, dexp2}, ty);
      then
        (typedExp, ty, vr);


/**/ // abs(v)  Is expanded into  noEvent(if v >= 0 then v else –v)
     //  Argument v needs to be an Integer or Real expression. (or subtypes of those)
     //  Result type is Integer or Real depending on the input v
     //  If vectorized, v is an array
    case (Absyn.CREF_IDENT(name = "abs"), Absyn.FUNCTIONARGS(args = {aexp1}))
      algorithm
        (dexp1, ty1, vr1) := NFTyping.typeExp(aexp1, scope, component, info);
        try
          true := Types.isNumericType(ty1);
        else
          errorFailBuiltinWrongArgTypes(functionName, functionArgs,
            "Integer or Real argument expected", info);
        end try;
        typedExp := Expression.makePureBuiltinCall("abs", {dexp1}, ty1);
      then
        (typedExp, ty1, vr1);

 //??petfr:

  // array(A,B,C,...) constructs an array from its arguments
  // All arguments must have the same sizes, i.e., size(A)=size(B)=size(C)=...
  // All arguments must be type compatible expressions
  // There must be at least one argument [i.e., array() or {} is not defined
  // {A, B, C, ...} is a shorthand notation for array(A, B, C, ...)
  // array(alpha, 2, 3.0) or {alpha, 2, 3.0} is a 3-vector of type Real.
  // Angle[3] a = {1.0, alpha, 4};   // type of a is Real[3]

  // petfr  ?? CHECK elabBuiltinArray in static.mo

 /**/  //  case (Absyn.CREF_IDENT(name = "array"), Absyn.FUNCTIONARGS(args = afargs))
 // OLD:  ??OBS: this code is not updated yet
/*      equation
        call_path = Absyn.crefToPath(functionName);
        (pos_args, globals) = NFTyping.typeExps(afargs, inEnv, inPrefix, inInfo, globals);
      then
        DAE.CALL(call_path, pos_args, DAE.callAttrBuiltinOther);
*/


    /* adrpo: adapt these to the new structures, see above
 **   case (Absyn.CREF_IDENT(name = "product"), Absyn.FUNCTIONARGS(args = afargs))
      equation
        call_path = Absyn.crefToPath(functionName);
        (pos_args, globals) = NFTyping.typeExps(afargs, inEnv, inPrefix, inInfo, globals);
      then
        DAE.CALL(call_path, pos_args, DAE.callAttrBuiltinOther);

    // pre(y) returns left limit y(tpre) of variable y(t) at a time instant t
 **    case (Absyn.CREF_IDENT(name = "pre"), Absyn.FUNCTIONARGS(args = afargs))
      equation
        call_path = Absyn.crefToPath(functionName);
        (pos_args, globals) = NFTyping.typeExps(afargs, inEnv, inPrefix, inInfo, globals);
      then
        DAE.CALL(call_path, pos_args, DAE.callAttrBuiltinOther);


 **   case (Absyn.CREF_IDENT(name = "noEvent"), Absyn.FUNCTIONARGS(args = afargs))
      equation
        call_path = Absyn.crefToPath(functionName);
        (pos_args, globals) = NFTyping.typeExps(afargs, inEnv, inPrefix, inInfo, globals);
      then
        DAE.CALL(call_path, pos_args, DAE.callAttrBuiltinOther);

    // sum(A) Returns the scalar sum of all the elements of array expression
 **   case (Absyn.CREF_IDENT(name = "sum"), Absyn.FUNCTIONARGS(args = afargs))
      equation
        call_path = Absyn.crefToPath(functionName);
        (pos_args, globals) = NFTyping.typeExps(afargs, inEnv, inPrefix, inInfo, globals);
      then
        DAE.CALL(call_path, pos_args, DAE.callAttrBuiltinOther);

  // Example:  assert(size(a,1)==size(a,2),"Matrix must be square");
  //   assert(condition, message); // Uses level=AssertionLevel.error
  //   assert(condition, message, assertionLevel);
  //   assert(condition, message, level = assertionLevel);
  //  ?? an assert statement has no type, or we just ignore it?
 **   case (Absyn.CREF_IDENT(name = "assert"), Absyn.FUNCTIONARGS(args = afargs))
      equation
        call_path = Absyn.crefToPath(functionName);
        (pos_args, globals) = NFTyping.typeExps(afargs, inEnv, inPrefix, inInfo, globals);
      then
        DAE.CALL(call_path, pos_args, DAE.callAttrBuiltinOther);

 **   case (Absyn.CREF_IDENT(name = "change"), Absyn.FUNCTIONARGS(args = afargs))
      equation
        call_path = Absyn.crefToPath(functionName);
        (pos_args, globals) = NFTyping.typeExps(afargs, inEnv, inPrefix, inInfo, globals);
      then
        DAE.CALL(call_path, pos_args, DAE.callAttrBuiltinOther);

 **   case (Absyn.CREF_IDENT(name = "array"), Absyn.FUNCTIONARGS(args = afargs))
      equation
        call_path = Absyn.crefToPath(functionName);
        (pos_args, globals) = NFTyping.typeExps(afargs, inEnv, inPrefix, inInfo, globals);
      then
        DAE.CALL(call_path, pos_args, DAE.callAttrBuiltinOther);


// array "(" expression for iterators ")"
// is an array constructor with iterators.
// The expressions inside the iterators of an array constructor shall be vector expressions
//Example: array(i for i in 1:10)
// Gives the vector 1:10={1,2,3,...,10}
//Example: {r for r in 1.0 : 1.5 : 5.5}
// Gives the vector 1.0:1.5:5.5={1.0, 2.5, 4.0, 5.5}
//Example: Real hilb[:,:]= {(1/(i+j-1) for i in 1:n, j in 1:n};
    case (Absyn.CREF_IDENT(name = "array"), Absyn.FOR_ITER_FARG(exp=aexp1, iterators=iters))
      equation
        call_path = Absyn.crefToPath(functionName);
        env = NFSCodeEnv.extendEnvWithIterators(iters, System.tmpTickIndex(NFSCodeEnv.tmpTickIndex), inEnv);
        (dexp1, globals) = NFTyping.typeExp(aexp1, env, inPrefix, inInfo, globals);
      then
        DAE.CALL(call_path, {dexp1}, DAE.callAttrBuiltinOther);

   // sum( e(i, ..., j) for  i in u, ...,  j in v)
    case (Absyn.CREF_IDENT(name = "sum"), Absyn.FOR_ITER_FARG(exp=aexp1, iterators=iters))
      equation
        call_path = Absyn.crefToPath(functionName);
        env = NFSCodeEnv.extendEnvWithIterators(iters, System.tmpTickIndex(NFSCodeEnv.tmpTickIndex), inEnv);
        (dexp1, globals) = NFTyping.typeExp(aexp1, env, inPrefix, inInfo, globals);
      then
        DAE.CALL(call_path, {dexp1}, DAE.callAttrBuiltinOther);

    // min( e(i, ..., j) for  i in u, ...,  j in v)
    case (Absyn.CREF_IDENT(name = "min"), Absyn.FOR_ITER_FARG(exp=aexp1, iterators=iters))
      equation
        call_path = Absyn.crefToPath(functionName);
        env = NFSCodeEnv.extendEnvWithIterators(iters, System.tmpTickIndex(NFSCodeEnv.tmpTickIndex), inEnv);
        (dexp1, globals) = NFTyping.typeExp(aexp1, env, inPrefix, inInfo, globals);
      then
        DAE.CALL(call_path, {dexp1}, DAE.callAttrBuiltinOther);

    // max( e(i, ..., j) for  i in u, ...,  j in v)
    case (Absyn.CREF_IDENT(name = "max"), Absyn.FOR_ITER_FARG(exp=aexp1, iterators=iters))
      equation
        call_path = Absyn.crefToPath(functionName);
        env = NFSCodeEnv.extendEnvWithIterators(iters, System.tmpTickIndex(NFSCodeEnv.tmpTickIndex), inEnv);
        (dexp1, globals) = NFTyping.typeExp(aexp1, env, inPrefix, inInfo, globals);
      then
        DAE.CALL(call_path, {dexp1}, DAE.callAttrBuiltinOther);

   // The type of product(e(i, ..., j) for i in u, ..., j in v) is the same as the type of e(i,...j)
    case (Absyn.CREF_IDENT(name = "product"), Absyn.FOR_ITER_FARG(exp=aexp1, iterators=iters))
      equation
        call_path = Absyn.crefToPath(functionName);
        env = NFSCodeEnv.extendEnvWithIterators(iters, System.tmpTickIndex(NFSCodeEnv.tmpTickIndex), inEnv);
        (dexp1, globals) = NFTyping.typeExp(aexp1, env, inPrefix, inInfo, globals);
      then
        DAE.CALL(call_path, {dexp1}, DAE.callAttrBuiltinOther);

   // function cat(k,A,B,C,...) concatenates arrays A,B,C,... along dimension k
   // Arrays A, B, C, ... must have the same number of dimensions, i.e., ndims(A) =  ndims(B) =
   // Arrays A, B, C, ... must be type compatible expressions, integers can become reals
   // k has to characterize an existing dimension, i.e., 1 <= k <= ndims(A) = ndims(B) = ndims(C);
   // Size matching: Arrays A, B, C, ... must have identical array sizes with the exception of the size
   // of dimension k, i.e., size(A,j) = size(B,j), for 1 <= j <= ndims(A) and j <> k
   // Example: Real[2,3]  r1  = cat(1, {{1.0, 2.0, 3}}, {{4, 5, 6}});
   // Example: Real[2,6]  r2  = cat(2, r1, 2*r1);
    case (Absyn.CREF_IDENT(name = "cat"), Absyn.FUNCTIONARGS(args = afargs))
      equation
        call_path = Absyn.crefToPath(functionName);
        (pos_args, globals) = NFTyping.typeExps(afargs, inEnv, inPrefix, inInfo, globals);
      then
        DAE.CALL(call_path, pos_args, DAE.callAttrBuiltinOther);

  // actualStream(v) returns the actual value of the stream variable v för any flow direction
  // actualStream(port.h_outflow) = if port.m_flow > 0 then inStream(port.h_outflow) else port.h_outflow;
  // The operator is vectorizable.
    case (Absyn.CREF_IDENT(name = "actualStream"), Absyn.FUNCTIONARGS(args = afargs))
      equation
        call_path = Absyn.crefToPath(functionName);
        (pos_args, globals) = NFTyping.typeExps(afargs, inEnv, inPrefix, inInfo, globals);
      then
        DAE.CALL(call_path, pos_args, DAE.callAttrBuiltinOther);

  // inStream(v)  is only allowed on stream variables v defined in stream connectors,
  // and is the value of the stream variable v close to the connection point
  // The operator is vectorizable.
    case (Absyn.CREF_IDENT(name = "inStream"), Absyn.FUNCTIONARGS(args = afargs))
      equation
        call_path = Absyn.crefToPath(functionName);
        (pos_args, globals) = NFTyping.typeExps(afargs, inEnv, inPrefix, inInfo, globals);
      then
        DAE.CALL(call_path, pos_args, DAE.callAttrBuiltinOther);

  // String(b, <options>),   String(i, <options>),  String(r, format=s),   String(e, <options>)
  // String(r, significantDigits=d,  <options>)
  // Convert a scalar non-String expression to a String representation.
  // For Real expressions the output shall be according to the Modelica grammar.
  // String(E.enumvalue) string of enum value, e.g. String(E.Small) gives "Small".
  // The first argument may be a Boolean b, an Integer i, a Real r or an Enumeration e).
  // The other arguments must use named arguments. The optional <options> are:
  //  Integer minimumLength=0: minimum length of the resulting string.
  //  Boolean leftJustified = true
  //  Integer significantDigits=6 defines the number of significant digits in the result string
    case (Absyn.CREF_IDENT(name = "String"), Absyn.FUNCTIONARGS(args = afargs))
      equation
        call_path = Absyn.crefToPath(functionName);
        (pos_args, globals) = NFTyping.typeExps(afargs, inEnv, inPrefix, inInfo, globals);
      then
        DAE.CALL(call_path, pos_args, DAE.callAttrBuiltinOther);


  // Integer(e) Returns the ordinal Integer number of the expression e of enumeration type
  // that evaluates to the enumeration value E.enumvalue, where Integer(E.e1)=1,
  // Integer(E.en)= n, for an enumeration type E=enumeration(e1, ..., en)
    case (Absyn.CREF_IDENT(name = "Integer"), Absyn.FUNCTIONARGS(args = afargs))
      equation
        call_path = Absyn.crefToPath(functionName);
        (pos_args, globals) = NFTyping.typeExps(afargs, inEnv, inPrefix, inInfo, globals);
      then
        DAE.CALL(call_path, pos_args, DAE.callAttrBuiltinOther);

  // Real(e) ?? is there a Real conversion function?, could not find it in the 3.3 rev1 spec
    case (Absyn.CREF_IDENT(name = "Real"), Absyn.FUNCTIONARGS(args = afargs))
      equation
        call_path = Absyn.crefToPath(functionName);
        (pos_args, globals) = NFTyping.typeExps(afargs, inEnv, inPrefix, inInfo, globals);
      then
        DAE.CALL(call_path, pos_args, DAE.callAttrBuiltinOther);


    */

    // TODO! FIXME!
    // check if more functions need to be handled here
    // we also need to handle Absyn.FOR_ITER_FARG reductions instead of Absyn.FUNCTIONARGS

    /*
    // adrpo: no support for $overload functions yet: div, mod, rem, abs, i.e. ModelicaBuiltin.mo:
    // function mod = $overload(OpenModelica.Internal.intMod,OpenModelica.Internal.realMod)

**    // rem(x,y)  Returns the integer remainder of x/y, such that div(x,y)*y + rem(x, y) = x.
    //   Result and arguments shall have type Real or Integer.
    //   If either of the arguments is Real the result is Real otherwise Integer.
    case (Absyn.CREF_IDENT(name = "rem"), Absyn.FUNCTIONARGS(args = afargs))
      equation
        call_path = Absyn.crefToPath(functionName);
        (pos_args, globals) = NFTyping.typeExps(afargs, inEnv, inPrefix, inInfo, globals);
      then
        DAE.CALL(call_path, pos_args, DAE.callAttrBuiltinOther);

 **   // div(x,y)  Returns the algebraic quotient x/y with any fractional part discarded
    //   Result and arguments shall have type Real or Integer.
    //   If either of the arguments is Real the result is Real otherwise Integer

 **   // mod(x,y)  Returns the integer modulus of x/y, i.e. mod(x,y)=x-floor(x/y)*y
    //   Result and arguments shall have type Real or Integer.
    //   If either of the arguments is Real the result is Real otherwise Integer

 **   // abs(v)  Is expanded into  noEvent(if v >= 0 then v else –v)
    //   Argument v needs to be an Integer or Real expression.
    //   Result type is Integer or Real depending on the input v
    case (Absyn.CREF_IDENT(name = "abs"), Absyn.FUNCTIONARGS(args = afargs))
      equation
        call_path = Absyn.crefToPath(functionName);
        (pos_args, globals) = NFTyping.typeExps(afargs, inEnv, inPrefix, inInfo, globals);
      then
        DAE.CALL(call_path, pos_args, DAE.callAttrBuiltinOther);

    */

    // hopefully all the other ones have a complete entry in ModelicaBuiltin.mo
    case (_, _)
      algorithm
        (typedExp, ty, vr) := typeNormalFunction(functionName, functionArgs, prefix, classNode, classType, cls, scope, component, info);
      then
        (typedExp, ty, vr);

 end matchcontinue;
end typeBuiltinFunctionCall;


function errorFailBuiltinWrongArgTypes
"@author: petfr  Generate an error message and fail if wrong argument types to builtin function"
  input Absyn.ComponentRef functionName;
  input Absyn.FunctionArgs functionArgs;
  input String specialMsg;
  input SourceInfo info;
algorithm
  errorFailBuiltinSpecError(functionName, functionArgs, Error.ARG_TYPE_MISMATCH, specialMsg, info);
end errorFailBuiltinWrongArgTypes;


function errorFailBuiltinSpecError
"@author: petfr  Generate an error message and fail if specified error for builtin function call"
  input Absyn.ComponentRef functionName;
  input Absyn.FunctionArgs functionArgs;
  input Error.Message errmsg;
  input String specialMsg;
  input SourceInfo info;
protected
  String fn_str, args_str;
algorithm
  fn_str := Dump.printComponentRefStr(functionName);
  args_str := Dump.printFunctionArgsStr(functionArgs);

  Error.addSourceMessage(errmsg,
    {" function: ", fn_str, "arguments: ", args_str, " ", specialMsg}, info);
  fail();
end errorFailBuiltinSpecError;



annotation(__OpenModelica_Interface="frontend");
end NFFunc;
