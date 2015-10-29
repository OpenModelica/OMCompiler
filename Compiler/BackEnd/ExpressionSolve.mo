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

encapsulated package ExpressionSolve
" file:        ExpressionSolve.mo
  package:     ExpressionSolve
  description: ExpressionSolve

  RCS: $Id$

  This file contains the module ExpressionSolve, which contains functions
  to solve a DAE.Exp for a DAE.Exp"

// public imports
public import Absyn;
public import DAE;

// protected imports
protected import ComponentReference;
protected import Debug;
protected import Differentiate;
protected import Expression;
protected import ExpressionDump;
protected import BackendDump;
protected import ExpressionSimplify;
protected import Flags;
protected import List;
protected import Inline;
protected import BackendEquation;
protected import BackendVariable;
protected import BackendDAEUtil;

// =============================================================================
// section for postOptModule >>solveSimpleEquations<<
//
// solve simple equations otherwise detect EQUATIONSYSTEM
// =============================================================================

public function solveSimpleEquations
  input BackendDAE.BackendDAE inDAE;
  output BackendDAE.BackendDAE outDAE;
algorithm
 (outDAE, _) := BackendDAEUtil.mapEqSystemAndFold(inDAE, findSimpleEquation0, false);
end solveSimpleEquations;

protected function findSimpleEquation0
  input BackendDAE.EqSystem isyst;
  input BackendDAE.Shared inShared;
  input Boolean inChanged;
  output BackendDAE.EqSystem osyst;
  output BackendDAE.Shared outShared;
  output Boolean outChanged;
protected
  BackendDAE.StrongComponents comps;
algorithm
  BackendDAE.EQSYSTEM(matching=BackendDAE.MATCHING(comps=comps)) := isyst;
  (osyst, outShared, outChanged) := findSimpleEquation1(isyst, inShared, comps, inChanged);
end findSimpleEquation0;

protected function findSimpleEquation1
  input BackendDAE.EqSystem isyst;
  input BackendDAE.Shared ishared;
  input BackendDAE.StrongComponents inComps;
  input Boolean inchanged;
  output BackendDAE.EqSystem osyst = isyst;
  output BackendDAE.Shared oshared = ishared;
  output Boolean changed = inchanged "not used";
protected
  Boolean b;
  BackendDAE.StrongComponent c;
  Integer i = 1;
  list<BackendDAE.Var> newVars = {};
algorithm
  for comp in inComps loop
    (osyst,oshared, newVars) := findSimpleEquationWork(osyst,oshared,comp, i, newVars);
    i := i + 1;
  end for;
  if  not listEmpty(newVars) then
    osyst.orderedVars := BackendVariable.addVars(newVars, osyst.orderedVars);
    osyst := BackendDAEUtil.setEqSystMatrices(osyst);
    //BackendDump.printEqSystem(osyst);
  end if;

end findSimpleEquation1;

protected function findSimpleEquationWork
  input BackendDAE.EqSystem isyst;
  input BackendDAE.Shared ishared;
  input BackendDAE.StrongComponent icomp;
  input Integer iter;
  input list<BackendDAE.Var> iNewVars;
  output BackendDAE.EqSystem osyst;
  output BackendDAE.Shared oshared;
  output list<BackendDAE.Var> oNewVars;
algorithm
  (osyst,oshared,oNewVars):=
  matchcontinue (isyst,ishared,icomp)
    local
      DAE.ComponentRef cr;
      list<DAE.ComponentRef> solveCr;
      BackendDAE.Variables vars;
      BackendDAE.EquationArray eqns, eqns_;
      BackendDAE.Equation eqn_;
      BackendDAE.Var var_;
      list<BackendDAE.Var> tmpvars;
      Integer eindex,vindx;
      BackendDAE.EqSystem syst;
      BackendDAE.Shared shared;
      DAE.ElementSource source;
      BackendDAE.Matching matching;
      DAE.FunctionTree funcs;
      list<BackendDAE.Equation> solveEqns;
      DAE.Exp e1,e2,varexp,e;
      list<DAE.Statement> asserts;
      BackendDAE.EquationAttributes attr;
      BackendDAE.StrongComponent comp;
      BackendDAE.StrongComponents comps;
      array<Integer> ass1, ass2;


    case (BackendDAE.EQSYSTEM(orderedVars=vars,orderedEqs=eqns,matching=matching),shared,BackendDAE.SINGLEEQUATION(eqn=eindex,var=vindx))
      algorithm
        (eqn_ as BackendDAE.EQUATION(exp=e1, scalar=e2, source=source,attr=attr)) := BackendEquation.equationNth1(eqns, eindex);
        (var_ as BackendDAE.VAR(varName = cr)) := BackendVariable.getVarAt(vars, vindx);

        varexp := Expression.crefExp(cr);
        varexp := if BackendVariable.isStateVar(var_) then Expression.expDer(varexp) else varexp;
        BackendDAE.SHARED(functionTree = funcs) := shared;
        tmpvars := iNewVars;
        try
          //TODO:
          //(e, asserts, solveEqns, solveCr) := ExpressionSolve.solve2(e1, e2, varexp, SOME(funcs), SOME(eindex));
          (e, asserts, solveEqns, solveCr) := ExpressionSolve.solve2(e1, e2, varexp, SOME(funcs), NONE());
          source := DAEUtil.addSymbolicTransformationSolve(true, source, cr, e1, e2, e, asserts);
           if listEmpty(solveEqns) then
             eqn_ := BackendDAE.EQUATION(varexp, e, source, attr);
           else
             solveCr := listReverse(solveCr);
             tmpvars := List.appendNoCopy(tmpvars, List.map(solveCr, BackendVariable.makeVar));
             eqn_ := BackendDAE.EQUATION(varexp, e, source, attr);
             solveEqns := eqn_::solveEqns;
             eqn_ := eqnLst2Alg(solveEqns,source,attr);
           end if;
        else
         try
           // ExpressionSolve fail!
           // try simplify equation
           (varexp, e, solveEqns, solveCr, _) := preprocessingSolve(e1, e2, varexp, NONE(), NONE(), 0);
           true := listEmpty(solveEqns);
           eqn_ := BackendDAE.EQUATION(varexp, e, source, attr);
         else
           eqn_ := eqn_;
         end try;
          // ExressionSolve can't solve eqn -> make equastion system
          comp := BackendDAE.EQUATIONSYSTEM({eindex}, {vindx},  BackendDAE.EMPTY_JACOBIAN() ,BackendDAE.JAC_NONLINEAR(), false);
          BackendDAE.MATCHING(comps = comps, ass1 = ass1, ass2 = ass2) := matching;
          comps := List.replaceAt(comp, iter, comps);
          matching := BackendDAE.MATCHING(ass1, ass2, comps);
        end try;
        eqns_ := BackendEquation.setAtIndex(eqns, eindex, eqn_);
        syst := BackendDAEUtil.setEqSystEqs(isyst, eqns_);
        syst := BackendDAEUtil.setEqSystMatching(syst, matching);
        then(syst, shared, tmpvars);

    else (isyst, ishared, iNewVars);
  end matchcontinue;
end findSimpleEquationWork;

public function eqnLst2Alg
  input list<BackendDAE.Equation> eqns;
  input DAE.ElementSource source;
  input BackendDAE.EquationAttributes attr;
  output BackendDAE.Equation alg;
protected
  Integer len = 0;
  DAE.ElementSource source_ = DAE.emptyElementSource;
  //EquationAttributes attr_ := BackendDAE.EQ_ATTR_DEFAULT_UNKNOWN;
  DAE.Expand expand = DAE.NOT_EXPAND();
  DAE.Exp e1,e2,e11,e22;
  list<DAE.Statement> statementLst = {};
  DAE.Type tp;
  DAE.Algorithm alg_;
  DAE.ComponentRef cr;
algorithm

  for eqn in eqns loop
    try
      BackendDAE.EQUATION(exp=e1, scalar=e2, source=source_) := eqn;
    else
      BackendDAE.SOLVED_EQUATION(cr, e2, source=source_) := eqn;
      e1 := Expression.crefExp(cr);
    end try;
    tp := Expression.typeof(e1);
    statementLst := DAE.STMT_ASSIGN(type_ = tp, exp1 = e1, exp = e2, source = source_) :: statementLst;
    len := len + 1;
  end for;

  alg_ := DAE.ALGORITHM_STMTS(statementLst=statementLst);
  alg := BackendDAE.ALGORITHM(len,
                              alg_,
                              source, expand, attr);

end eqnLst2Alg;

public function solve
"Solves an equation consisting of a right hand side (rhs) and a
  left hand side (lhs), with respect to the expression given as
  third argument, usually a variable."
  input DAE.Exp inExp1 "lhs";
  input DAE.Exp inExp2 "rhs";
  input DAE.Exp inExp3 "DAE.CREF or 'der(DAE.CREF())'";
  output DAE.Exp outExp;
  output list<DAE.Statement> outAsserts;
protected
  list<BackendDAE.Equation> dummy1;
  list<DAE.ComponentRef> dummy2;
  Integer dummyI;
algorithm
/*
  print("Try to solve: rhs: " +
  ExpressionDump.dumpExpStr(inExp1,0) + " lhs: " +
  ExpressionDump.dumpExpStr(inExp2,0) + " with respect to: " +
  ExpressionDump.printExpStr(inExp3) + "\n");
*/
  (outExp,outAsserts,dummy1, dummy2, dummyI) := matchcontinue inExp1
    case _ then solveSimple(inExp1, inExp2, inExp3, 0);
    case _ then solveSimple(inExp2, inExp1, inExp3, 0);
    case _ then solveWork(inExp1, inExp2, inExp3, NONE(), NONE(), 0);
    else equation
      if Flags.isSet(Flags.FAILTRACE) then
        Error.addInternalError("Failed to solve \"" + ExpressionDump.printExpStr(inExp1) + " = " + ExpressionDump.printExpStr(inExp2) + "\" w.r.t. \"" + ExpressionDump.printExpStr(inExp3) + "\"", sourceInfo());
      end if;
    then fail();
  end matchcontinue;

 (outExp,_) := ExpressionSimplify.simplify1(outExp);
end solve;


public function solve2
"Solves an equation with modelica function consisting of a right hand side (rhs) and a
  left hand side (lhs), with respect to the expression given as
  third argument, usually a variable.
"
  input DAE.Exp inExp1 "lhs";
  input DAE.Exp inExp2 "rhs";
  input DAE.Exp inExp3 "DAE.CREF or 'der(DAE.CREF())'";
  input Option<DAE.FunctionTree> functions "need for solve modelica functions";
  input Option<Integer> uniqueEqIndex "offset for tmp vars";
  output DAE.Exp outExp;
  output list<DAE.Statement> outAsserts;
  output list<BackendDAE.Equation> eqnForNewVars "eqn for tmp vars";
  output list<DAE.ComponentRef> newVarsCrefs;
protected
  Integer dummyI;
algorithm
/*
  print("Try to solve: rhs: " +
  ExpressionDump.dumpExpStr(inExp1,0) + " lhs: " +
  ExpressionDump.dumpExpStr(inExp2,0) + " with respect to: " +
  ExpressionDump.printExpStr(inExp3) + "\n");
*/
  (outExp,outAsserts,eqnForNewVars,newVarsCrefs,dummyI) := matchcontinue inExp1
    case _ then solveSimple(inExp1, inExp2, inExp3, 0);
    case _ then solveSimple(inExp2, inExp1, inExp3, 0);
    case _ then solveWork(inExp1, inExp2, inExp3, functions, uniqueEqIndex, 0);
    else equation
      if Flags.isSet(Flags.FAILTRACE) then
        Error.addInternalError("Failed to solve \"" + ExpressionDump.printExpStr(inExp1) + " = " + ExpressionDump.printExpStr(inExp2) + "\" w.r.t. \"" + ExpressionDump.printExpStr(inExp3) + "\"", sourceInfo());
      end if;
    then fail();
  end matchcontinue;

  outExp := symEuler_helper(outExp, inExp3);
  (outExp,_) := ExpressionSimplify.simplify1(outExp);
end solve2;


protected function solveWork

 input DAE.Exp inExp1 "lhs";
 input DAE.Exp inExp2 "rhs";
 input DAE.Exp inExp3 "DAE.CREF or 'der(DAE.CREF())'";
 input Option<DAE.FunctionTree> functions;
 input Option<Integer> uniqueEqIndex "offset for tmp vars";
 input Integer idepth;
 output DAE.Exp outExp;
 output list<DAE.Statement> outAsserts;
 output list<BackendDAE.Equation> eqnForNewVars "eqn for tmp vars";
 output list<DAE.ComponentRef> newVarsCrefs;
 output Integer depth;


protected
 DAE.Exp e1, e2;
 list<BackendDAE.Equation> eqnForNewVars1;
 list<DAE.ComponentRef> newVarsCrefs1;
algorithm
 (e1, e2, eqnForNewVars, newVarsCrefs, depth) := matchcontinue(inExp1, inExp2, inExp3, functions, uniqueEqIndex)
               case(_,_,_,_,_) then preprocessingSolve(inExp1, inExp2, inExp3, functions, uniqueEqIndex, idepth);
               else
                equation
                  if Flags.isSet(Flags.FAILTRACE) then
                    Debug.trace("\n-ExpressionSolve.preprocessingSolve failed:\n");
                    Debug.trace(ExpressionDump.printExpStr(inExp1) + " = " + ExpressionDump.printExpStr(inExp2));
                    Debug.trace(" with respect to: " + ExpressionDump.printExpStr(inExp3));
                  end if;
                then (inExp1,inExp2,{},{}, idepth);
              end matchcontinue;

 (outExp, outAsserts, eqnForNewVars1, newVarsCrefs1, depth) := matchcontinue(e1, e2, inExp3)
                          case(DAE.IFEXP(),_,_) then  solveIfExp(e1, e2, inExp3, functions, uniqueEqIndex, depth);
                          case(_,_,_) then  solveSimple(e1, e2, inExp3, depth);
                          case(_,_,_) then  solveLinearSystem(e1, e2, inExp3, functions, depth);
                          else fail();
                         end matchcontinue;

 eqnForNewVars := List.appendNoCopy(eqnForNewVars, eqnForNewVars1);
 newVarsCrefs := List.appendNoCopy(newVarsCrefs, newVarsCrefs1);

end solveWork;

public function solveLin
"function: solve linear equation
  Solves an equation consisting of a right hand side (rhs) and a
  left hand side (lhs), with respect to the expression given as
  third argument, usually a variable."
  input DAE.Exp inExp1;
  input DAE.Exp inExp2;
  input DAE.Exp inExp3;
  output DAE.Exp outExp;
  output list<DAE.Statement> outAsserts;
algorithm
  (outExp,outAsserts) := matchcontinue(inExp1, inExp2, inExp3)
                         case(_,_,_) then solve(inExp1,inExp2,inExp3);
                         else
                          equation
                            if Flags.isSet(Flags.FAILTRACE) then
                              Debug.trace("\n-ExpressionSolve.solveLin failed:\n");
                              Debug.trace(ExpressionDump.printExpStr(inExp1) + " = " + ExpressionDump.printExpStr(inExp2));
                              Debug.trace(" with respect to: " + ExpressionDump.printExpStr(inExp3));
                            end if;
                            then fail();
                        end matchcontinue;
end solveLin;

protected function solveSimple
"Solves simple equations like
  a = f(..)
  der(a) = f(..)
  -a = f(..)
  -der(a) = f(..)"
  input DAE.Exp inExp1 "lhs";
  input DAE.Exp inExp2 "rhs";
  input DAE.Exp inExp3 "DAE.CREF or 'der(DAE.CREF())'";
  input Integer idepth;
  output DAE.Exp outExp;
  output list<DAE.Statement> outAsserts;
  output list<BackendDAE.Equation> eqnForNewVars = {} "eqn for tmp vars";
  output list<DAE.ComponentRef> newVarsCrefs = {};
  output Integer odepth = idepth;

algorithm

 /*
  print("Try to solve: rhs: " +
  ExpressionDump.dumpExpStr(inExp1,0) + " lhs: " +
  ExpressionDump.dumpExpStr(inExp2,0) + " with respect to: " +
  ExpressionDump.printExpStr(inExp3) + "\n");
*/

  (outExp,outAsserts) := match (inExp1,inExp2,inExp3)
    local
      DAE.ComponentRef cr,cr1;
      DAE.Type tp;
      DAE.Exp e1,e2,res,e11;
      Real r, r2;
      list<DAE.Statement> asserts;

    // special case for inital system when already solved, cr1 = $_start(...)
    case (DAE.CREF(componentRef = cr1),DAE.CALL(path = Absyn.IDENT(name = "$_start")),DAE.CREF(componentRef = cr))
      equation
        true = ComponentReference.crefEqual(cr, cr1);
      then
        (inExp2,{});
    case (DAE.CALL(path = Absyn.IDENT(name = "der"),expLst = {DAE.CREF(componentRef = cr1)}),DAE.CALL(path = Absyn.IDENT(name = "$_start")),DAE.CREF(componentRef = cr))
      equation
        true = ComponentReference.crefEqual(cr, cr1);
      then
        (inExp2,{});

    // special case when already solved, cr1 = rhs, otherwise division by zero when dividing with derivative
    case (DAE.CREF(componentRef = cr1),_,DAE.CREF(componentRef = cr))
      equation
        true = ComponentReference.crefEqual(cr, cr1);
        false = Expression.expHasCrefNoPreOrStart(inExp2, cr);
      then
        (inExp2,{});
    case (DAE.CALL(path = Absyn.IDENT(name = "der"),expLst = {DAE.CREF(componentRef = cr1)}),_,DAE.CALL(path = Absyn.IDENT(name = "der"),expLst = {DAE.CREF(componentRef = cr)}))
      equation
        true = ComponentReference.crefEqual(cr, cr1);
        false = Expression.expHasDerCref(inExp2, cr);
      then
        (inExp2,{});

    // -cr = exp
    case (DAE.UNARY(operator = DAE.UMINUS(), exp = DAE.CREF(componentRef = cr1)),_,DAE.CREF(componentRef = cr))
      equation
        true = ComponentReference.crefEqual(cr1,cr);
        // cr not in e2
        false = Expression.expHasCrefNoPreOrStart(inExp2,cr);
      then
        (Expression.negate(inExp2),{});
    case (DAE.UNARY(operator = DAE.UMINUS_ARR(), exp = DAE.CREF(componentRef = cr1)),_,DAE.CREF(componentRef = cr))
      equation
        true = ComponentReference.crefEqual(cr1,cr);
        // cr not in e2
        false = Expression.expHasCrefNoPreOrStart(inExp2,cr);
      then
        (Expression.negate(inExp2),{});
    case (DAE.UNARY(operator = DAE.UMINUS(), exp = DAE.CALL(path = Absyn.IDENT(name = "der"),expLst = {DAE.CREF(componentRef = cr1)})),_,DAE.CALL(path = Absyn.IDENT(name = "der"),expLst = {DAE.CREF(componentRef = cr)}))
      equation
        true = ComponentReference.crefEqual(cr1,cr);
        // cr not in e2
        false = Expression.expHasDerCref(inExp2,cr);
      then
        (Expression.negate(inExp2),{});
    case (DAE.UNARY(operator = DAE.UMINUS_ARR(), exp = DAE.CALL(path = Absyn.IDENT(name = "der"),expLst = {DAE.CREF(componentRef = cr1)})),_,DAE.CALL(path = Absyn.IDENT(name = "der"),expLst = {DAE.CREF(componentRef = cr)}))
      equation
        true = ComponentReference.crefEqual(cr1,cr);
        // cr not in e2
        false = Expression.expHasDerCref(inExp2,cr);
      then
        (Expression.negate(inExp2),{});

    // !cr = exp
    case (DAE.LUNARY(operator = DAE.NOT(), exp = DAE.CREF(componentRef = cr1)),_,DAE.CREF(componentRef = cr))
      equation
        true = ComponentReference.crefEqual(cr1,cr);
        // cr not in e2
        false = Expression.expHasCrefNoPreOrStart(inExp2,cr);
      then
        (Expression.negate(inExp2),{});

    // Integer(enumcr) = ...
    case (DAE.CALL(path = Absyn.IDENT(name = "Integer"),expLst={DAE.CREF(componentRef = cr1)}),_,DAE.CREF(componentRef = cr,ty=tp))
      equation
        true = ComponentReference.crefEqual(cr, cr1);
        // cr not in e2
        false = Expression.expHasCrefNoPreorDer(inExp2,cr);
        asserts = generateAssertType(tp,cr,inExp3,{});
      then (DAE.CAST(tp,inExp2),asserts);
      else fail();
  end match;
end solveSimple;

protected function generateAssertType
  input DAE.Type tp;
  input DAE.ComponentRef cr;
  input DAE.Exp iExp;
  input list<DAE.Statement> inAsserts;
  output list<DAE.Statement> outAsserts;
algorithm
  outAsserts := match(tp,cr,iExp,inAsserts)
    local
      Absyn.Path path,p1,pn;
      list<String> names;
      Integer n;
      DAE.Exp e1,en,e,es;
      String s1,sn,se,estr,crstr;
    case (DAE.T_ENUMERATION(path=path,names=names),_,_,_)
      equation
        p1 = Absyn.suffixPath(path,listHead(names));
        e1 = DAE.ENUM_LITERAL(p1,1);
        n = listLength(names);
        pn = Absyn.suffixPath(path,listGet(names,n));
        en = DAE.ENUM_LITERAL(p1,n);
        s1 = Absyn.pathString(p1);
        sn = Absyn.pathString(pn);
        _ = ExpressionDump.printExpStr(iExp);
        crstr = ComponentReference.printComponentRefStr(cr);
        estr = "Expression for " + crstr + " out of min(" + s1 + ")/max(" + sn + ") = ";
        // iExp >= e1 and iExp <= en
        e = DAE.LBINARY(DAE.RELATION(iExp,DAE.GREATEREQ(DAE.T_INTEGER_DEFAULT),e1,-1,NONE()),DAE.AND(DAE.T_BOOL_DEFAULT),
                                     DAE.RELATION(iExp,DAE.LESSEQ(DAE.T_INTEGER_DEFAULT),en,-1,NONE()));
        es = Expression.makePureBuiltinCall("String", {iExp,DAE.SCONST("d")}, DAE.T_STRING_DEFAULT);
        es = DAE.BINARY(DAE.SCONST(estr),DAE.ADD(DAE.T_STRING_DEFAULT),es);
      then
        DAE.STMT_ASSERT(e,es,DAE.ASSERTIONLEVEL_ERROR,DAE.emptyElementSource)::inAsserts;
    else inAsserts;
  end match;
end generateAssertType;

public function preprocessingSolve
"
preprocessing for solve1,
 sorting and split terms , with respect to the expression given as
 third argument.

 {f(x,y), g(x,y),x} -> {h(x), k(y)}

 author: Vitalij Ruge
"

  input DAE.Exp inExp1 "lhs";
  input DAE.Exp inExp2 "rhs";
  input DAE.Exp inExp3 "DAE.CREF or 'der(DAE.CREF())'";
  input Option<DAE.FunctionTree> functions;
  input Option<Integer> uniqueEqIndex "offset for tmp vars";
  input Integer idepth;
  output DAE.Exp h;
  output DAE.Exp k;
  output list<BackendDAE.Equation> eqnForNewVars = {} "eqn for tmp vars";
  output list<DAE.ComponentRef> newVarsCrefs = {};
  output Integer depth = idepth;

 protected
  DAE.Exp res;
  list<DAE.Exp> lhs, rhs, resTerms;
  list<DAE.Exp> lhsWithX, rhsWithX, lhsWithoutX, rhsWithoutX, eWithX, factorWithX, factorWithoutX;
  DAE.Exp lhsX, rhsX, lhsY, rhsY, x, y, N;
  DAE.ComponentRef cr;
  DAE.Boolean con, new_x, collect = true, inlineFun = true;
  Integer iter;

 algorithm
   (x, _) := ExpressionSimplify.simplify(inExp1);
   (y, _) := ExpressionSimplify.simplify(inExp2);
   res := Expression.expSub(x, y);
   resTerms :=  Expression.terms(res);

   // split and sort
   (lhsX, lhsY) := preprocessingSolve5(inExp1, inExp3,true);
   (rhsX, rhsY) := preprocessingSolve5(inExp2, inExp3,true);
   x := Expression.expSub(lhsX, rhsX);
   y := Expression.expSub(rhsY, lhsY);

   con := true;
   iter := 0;

   x := unifyFunCalls(x, inExp3);
   while con and iter < 1000 loop

     (x, y, con) := preprocessingSolve2(x,y, inExp3);
     (x, y, new_x) := preprocessingSolve3(x,y, inExp3);
     con := con or new_x;
     while new_x loop
       (x, y, new_x) := preprocessingSolve3(x,y, inExp3);
     end while;
     (x, y, new_x) := removeSimpleCalls(x,y, inExp3);
     con := con or new_x;
     (x, y, new_x) := preprocessingSolve4(x,y, inExp3);
     con := new_x or con;
     // TODO: use new defined function, which missing in the cpp runtime
     if not stringEqual(Config.simCodeTarget(), "Cpp") then
       (x, y, new_x, eqnForNewVars, newVarsCrefs, depth) := preprocessingSolveTmpVars(x, y, inExp3, uniqueEqIndex, eqnForNewVars, newVarsCrefs, depth);
     con := new_x or con;
     end if;

     if not con then
       (x, con) := ExpressionSimplify.simplify(x);
       // Z/N = rhs -> Z = rhs*N
       (x,N) := Expression.makeFraction(x);
       if not Expression.isOne(N) then
         //print("\nx ");print(ExpressionDump.printExpStr(x));print("\nN ");print(ExpressionDump.printExpStr(N));
         new_x := true;
         y := Expression.expMul(y,N);
       end if;

       con := new_x or con;
       iter := iter + 50;
     end if;

     if con and collect then
       (lhsX, lhsY) := preprocessingSolve5(x, inExp3, true);
       (rhsX, rhsY) := preprocessingSolve5(y, inExp3, false);
       x := Expression.expSub(lhsX, rhsX);
       y := Expression.expSub(rhsY, lhsY);
       collect := true;
     elseif collect then
       collect := false;
       con := true;
       iter := iter + 50;
     elseif inlineFun then
       (x,con) := solveFunCalls(x, inExp3, functions);
       collect := con;
       inlineFun := false;
     end if;

     if con and collect then
       (lhsX, lhsY) := preprocessingSolve5(x, inExp3, true);
       (rhsX, rhsY) := preprocessingSolve5(y, inExp3, false);
       x := Expression.expSub(lhsX, rhsX);
       y := Expression.expSub(rhsY, lhsY);
     end if;

     iter := iter + 1;
     //print("\nx ");print(ExpressionDump.printExpStr(x));print("\ny ");print(ExpressionDump.printExpStr(y));
   end while;

   (k,_) := ExpressionSimplify.simplify1(y);

   // h(x) = k(y)
   (h,_) := ExpressionSimplify.simplify(x);

/*
   if not Expression.expEqual(inExp1,h) then
     print("\nIn: ");print(ExpressionDump.printExpStr(inExp1));print(" = ");print(ExpressionDump.printExpStr(inExp2));
     print("\nOut: ");print(ExpressionDump.printExpStr(h));print(" = ");print(ExpressionDump.printExpStr(k));
     print("\t w.r.t ");print(ExpressionDump.printExpStr(inExp3));
   end if;
*/
end preprocessingSolve;

protected function symEuler_helper
"
 special case for symEuler
"
  input DAE.Exp rhs;
  input DAE.Exp X;
  output DAE.Exp orhs = rhs;
protected
  DAE.Type tp;
  DAE.Exp dt;
algorithm
  if Flags.getConfigBool(Flags.SYM_EULER) then
    dt := Expression.crefExp(ComponentReference.makeCrefIdent(BackendDAE.symEulerDT, DAE.T_REAL_DEFAULT, {}));
    if expHasCref(rhs, dt) then
      // x = dt != 0 ? k1(y,dt) : old_x
      tp := Expression.typeof(X);
      orhs := DAE.IFEXP(Expression.makeNoEvent(DAE.RELATION(
                dt,
                  DAE.EQUAL(tp),
                DAE.RCONST(0.0),-1,NONE())), X, rhs);
    end if;
  end if;

end symEuler_helper;

protected function preprocessingSolve2
"
 helprer function for preprocessingSolve
 e.g.
   x/(x+c1) = -c2 --> x + (x+c1)*c2 = 0

 author: Vitalij Ruge
"
  input DAE.Exp inExp1 "lhs";
  input DAE.Exp inExp2 "rhs";
  input DAE.Exp inExp3 "DAE.CREF or 'der(DAE.CREF())'";

  output DAE.Exp olhs;
  output DAE.Exp orhs;
  output Boolean con "continue";

algorithm

(olhs, orhs, con) := matchcontinue (inExp1,inExp2,inExp3)
    local
     DAE.Exp e,a, b, fb, fa, ga, lhs, rhs;
     DAE.Type tp;
     DAE.Operator op;
     list<DAE.Exp> eWithX, factorWithX, factorWithoutX;
     DAE.Exp pWithX, pWithoutX;

    // -f(a) = b => f(a) = -b
    case(DAE.UNARY(op as DAE.UMINUS(), fa),_,_)
      equation
        true = expHasCref(fa, inExp3);
        false = expHasCref(inExp2, inExp3);
        b = DAE.UNARY(op, inExp2);
    then(fa, b, true);
    case(DAE.UNARY(op as DAE.UMINUS_ARR(), fa),_,_)
      equation
        true = expHasCref(fa, inExp3);
        false = expHasCref(inExp2, inExp3);
        b = DAE.UNARY(op, inExp2);
    then(fa, b, true);

    // b/f(a) = rhs  => f(a) = b/rhs solve for a
    case(DAE.BINARY(b,DAE.DIV(_),fa), rhs, _)
      equation
        true = expHasCref(fa, inExp3);
        false = expHasCref(b, inExp3);
        false = expHasCref(rhs, inExp3);
        e = Expression.makeDiv(b, rhs);
      then(fa, e, true);

    // b*f(a) = rhs  => f(a) = rhs/b solve for a
    case(DAE.BINARY(b, DAE.MUL(_), fa), rhs, _)
      equation
        false = expHasCref(b, inExp3);
        true = expHasCref(fa, inExp3);
        false = expHasCref(rhs, inExp3);

        eWithX = Expression.expandFactors(inExp1);
        (factorWithX, factorWithoutX) = List.split1OnTrue(eWithX, expHasCref, inExp3);
        pWithX = makeProductLstSort(factorWithX);
        pWithoutX = makeProductLstSort(factorWithoutX);

        e = Expression.makeDiv(rhs, pWithoutX);

       then(pWithX, e, true);

    // b*a = rhs  => a = rhs/b solve for a
    case(DAE.BINARY(b, DAE.MUL(_), fa), rhs, _)
      equation
        false = expHasCref(b, inExp3);
        true = expHasCref(fa, inExp3);
        false = expHasCref(rhs, inExp3);
        e = Expression.makeDiv(rhs, b);
       then(fa, e, true);

    // a*b = rhs  => a = rhs/b solve for a
    case(DAE.BINARY(fa, DAE.MUL(_), b), rhs, _)
      equation
        false = expHasCref(b, inExp3);
        true = expHasCref(fa, inExp3);
        false = expHasCref(rhs, inExp3);
        e = Expression.makeDiv(rhs, b);
       then(fa, e, true);

    // f(a)/b = rhs  => f(a) = rhs*b solve for a
    case(DAE.BINARY(fa, DAE.DIV(_), b), rhs, _)
      equation
        true = expHasCref(fa, inExp3);
        false = expHasCref(b, inExp3);
        false = expHasCref(rhs, inExp3);
        e = Expression.expMul(rhs, b);
       then (fa, e, true);

    // g(a)/f(a) = rhs  => rhs*f(a) - g(a) = 0  solve for a
    case(DAE.BINARY(ga, DAE.DIV(tp), fa), rhs, _)
      equation
        true = expHasCref(fa, inExp3);
        true = expHasCref(ga, inExp3);
        false = expHasCref(rhs, inExp3);

        e = Expression.expMul(rhs, fa);
        lhs = Expression.expSub(e, ga);
        e = Expression.makeConstZero(tp);

       then(lhs, e, true);

   else (inExp1, inExp2, false);

   end matchcontinue;

end preprocessingSolve2;

protected function preprocessingSolve3
"
 helprer function for preprocessingSolve

 (r1)^f(a) = r2 => f(a)  = ln(r2)/ln(r1)
 f(a)^b = 0 => f(a) = 0
 f(a)^n = c => f(a) = c^(1/n)
 abs(x) = 0
 author: Vitalij Ruge
"
  input DAE.Exp inExp1 "lhs";
  input DAE.Exp inExp2 "rhs";
  input DAE.Exp inExp3 "DAE.CREF or 'der(DAE.CREF())'";

  output DAE.Exp olhs;
  output DAE.Exp orhs;
  output Boolean con "continue";

algorithm
  (olhs, orhs, con) := matchcontinue(inExp1, inExp2, inExp3)
      local
       Real r, r1, r2;
       DAE.Exp e1, e2, res;

      // (r1)^f(a) = r2 => f(a)  = ln(r2)/ln(r1)
      case (DAE.BINARY(e1 as DAE.RCONST(r1),DAE.POW(_),e2), DAE.RCONST(r2), _)
       equation
         true = r2 > 0.0;
         true = r1 > 0.0;
         false = Expression.isConstOne(e1);
         true = expHasCref(e2, inExp3);
         r = log(r2) / log(r1);
         res = DAE.RCONST(r);
       then
         (e2, res, true);

      // f(a)^b = 0 => f(a) = 0
      case (DAE.BINARY(e1,DAE.POW(_),e2), DAE.RCONST(real = 0.0), _)
        equation
         false = expHasCref(e2, inExp3);
         true = expHasCref(e1, inExp3);
       then
         (e1, inExp2, true);

      // f(a)^n = c => f(a) = c^(1/n)
      // where n is odd
      case (DAE.BINARY(e1,DAE.POW(_),e2 as DAE.RCONST(r)), _, _)
        equation
          false = expHasCref(inExp2, inExp3);
          true = expHasCref(e1, inExp3);
          1.0 = realMod(r,2.0);
          res = Expression.makeDiv(DAE.RCONST(1.0),e2);
          res = Expression.expPow(inExp2,res);
       then
         (e1, res, true);

      // sqrt(f(a)) = f(a)^n = c => f(a) = c^(1/n)
      case (DAE.BINARY(e1,DAE.POW(_),DAE.RCONST(0.5)), _, _)
        equation
          false = expHasCref(inExp2, inExp3);
          true = expHasCref(e1, inExp3);
          res = Expression.expPow(inExp2,DAE.RCONST(2.0));
       then
         (e1, res, true);

      // abs(x) = 0
      case (DAE.CALL(path = Absyn.IDENT(name = "abs"),expLst = {e1}), DAE.RCONST(0.0),_)
        then (e1,inExp2,true);

      // sign(x) = 0
      case (DAE.CALL(path = Absyn.IDENT(name = "sign"),expLst = {e1}), DAE.RCONST(0.0),_)
        then (e1,inExp2,true);


      else (inExp1, inExp2, false);

  end matchcontinue;


end preprocessingSolve3;


protected function preprocessingSolve4

"
 helprer function for preprocessingSolve

 e.g.
  sqrt(f(x)) - sqrt(g(x))) = 0 = f(x) - g(x)
  exp(f(x)) - exp(g(x))) = 0 = f(x) - g(x)

 author: Vitalij Ruge
"

  input DAE.Exp inExp1;
  input DAE.Exp inExp2;
  input DAE.Exp inExp3 "DAE.CREF or 'der(DAE.CREF())'";
  output DAE.Exp oExp1;
  output DAE.Exp oExp2;
  output Boolean newX;

algorithm

  (oExp1, oExp2, newX) := matchcontinue(inExp1, inExp2, inExp3)
          local
          String s1,s2;
          DAE.Operator op;
          DAE.Exp e1,e2,e3,e4, e, e_1, e_2;
          DAE.Type tp;

          // exp(f(x)) - exp(g(x)) = 0
          case(DAE.BINARY(DAE.CALL(path = Absyn.IDENT("exp"), expLst={e1}), DAE.SUB(_),
                          DAE.CALL(path = Absyn.IDENT("exp"), expLst={e2})),DAE.RCONST(0.0),_)
          then (e1, e2, true);
          // log(f(x)) - log(g(x)) = 0
          case(DAE.BINARY(DAE.CALL(path = Absyn.IDENT("log"), expLst={e1}), DAE.SUB(_),
                          DAE.CALL(path = Absyn.IDENT("log"), expLst={e2})),DAE.RCONST(0.0),_)
          then (e1, e2, true);
          // log10(f(x)) - log10(g(x)) = 0
          case(DAE.BINARY(DAE.CALL(path = Absyn.IDENT("log10"), expLst={e1}), DAE.SUB(_),
                          DAE.CALL(path = Absyn.IDENT("log10"), expLst={e2})),DAE.RCONST(0.0),_)
          then (e1, e2, true);
          // sinh(f(x)) - sinh(g(x)) = 0
          case(DAE.BINARY(DAE.CALL(path = Absyn.IDENT("sinh"), expLst={e1}), DAE.SUB(_),
                          DAE.CALL(path = Absyn.IDENT("sinh"), expLst={e2})),DAE.RCONST(0.0),_)
          then (e1, e2, true);
          // tanh(f(x)) - tanh(g(x)) = 0
          case(DAE.BINARY(DAE.CALL(path = Absyn.IDENT("tanh"), expLst={e1}), DAE.SUB(_),
                          DAE.CALL(path = Absyn.IDENT("tanh"), expLst={e2})),DAE.RCONST(0.0),_)
          then (e1, e2, true);
          // sqrt(f(x)) - sqrt(g(x)) = 0
          case(DAE.BINARY(DAE.CALL(path = Absyn.IDENT("sqrt"), expLst={e1}), DAE.SUB(_),
                          DAE.CALL(path = Absyn.IDENT("sqrt"), expLst={e2})),DAE.RCONST(0.0),_)
          then (e1, e2, true);

          // sinh(f(x)) - cosh(g(x)) = 0
          case(DAE.BINARY(DAE.CALL(path = Absyn.IDENT("sinh"), expLst={e1}), DAE.SUB(_),
                          DAE.CALL(path = Absyn.IDENT("cosh"), expLst={e2})),DAE.RCONST(0.0),_)
          equation
          true = Expression.expEqual(e1,e2);
          then (e1, inExp2, true);
          case(DAE.BINARY(DAE.CALL(path = Absyn.IDENT("cosh"), expLst={e1}), DAE.SUB(_),
                          DAE.CALL(path = Absyn.IDENT("sinh"), expLst={e2})),DAE.RCONST(0.0),_)
          equation
          true = Expression.expEqual(e1,e2);
          then (e1, inExp2, true);



         // y*sinh(x) - z*cosh(x) = 0
          case(DAE.BINARY(DAE.BINARY(e3,DAE.MUL(),DAE.CALL(path = Absyn.IDENT("sinh"), expLst={e1})), DAE.SUB(tp),
                          DAE.BINARY(e4,DAE.MUL(),DAE.CALL(path = Absyn.IDENT("cosh"), expLst={e2}))),DAE.RCONST(0.0),_)
          equation
          true = Expression.expEqual(e1,e2);
          e = Expression.makePureBuiltinCall("tanh",{e1},tp);
          then (Expression.expMul(e3,e), e4, true);
          case(DAE.BINARY(DAE.BINARY(e4,DAE.MUL(),DAE.CALL(path = Absyn.IDENT("cosh"), expLst={e2})), DAE.SUB(tp),
                          DAE.BINARY(e3,DAE.MUL(),DAE.CALL(path = Absyn.IDENT("sinh"), expLst={e1}))),DAE.RCONST(0.0),_)
          equation
          true = Expression.expEqual(e1,e2);
          e = Expression.makePureBuiltinCall("tanh",{e1},tp);
          then (Expression.expMul(e3,e), e4, true);



          // sqrt(x) - x = 0 -> x = x^2
          case(DAE.BINARY(DAE.CALL(path = Absyn.IDENT("sqrt"), expLst={e1}), DAE.SUB(_),e2), DAE.RCONST(0.0),_)
          then (e1, Expression.expPow(e2, DAE.RCONST(2.0)), true);
          case(DAE.BINARY(e2, DAE.SUB(_),DAE.CALL(path = Absyn.IDENT("sqrt"), expLst={e1})), DAE.RCONST(0.0),_)
          equation
          then (e1, Expression.expPow(e2, DAE.RCONST(2.0)), true);

          // f(x)^n - g(x)^n = 0 -> (f(x)/g(x))^n = 1
          case(DAE.BINARY(DAE.BINARY(e1, DAE.POW(), e2), DAE.SUB(tp), DAE.BINARY(e3, DAE.POW(), e4)), DAE.RCONST(0.0),_)
          equation
            true = Expression.expEqual(e2,e4);
            true = expHasCref(e1,inExp3);
            true = expHasCref(e3,inExp3);
            e = Expression.expPow(Expression.makeDiv(e1,e3),e2);
            (e_1, e_2, _) = preprocessingSolve3(e, Expression.makeConstOne(tp), inExp3);
          then (e_1, e_2, true);


          else (inExp1, inExp2, false);

    end matchcontinue;


end preprocessingSolve4;

protected function expAddX
"
 helprer function for preprocessingSolve

 if(y,g(x),h(x)) + x => if(y, g(x) + x, h(x) + x)
 a*f(x) + b*f(x) = (a+b)*f(x)
 author: Vitalij Ruge
"
  input DAE.Exp inExp1 "lhs";
  input DAE.Exp inExp2 "rhs";
  input DAE.Exp inExp3 "DAE.CREF or 'der(DAE.CREF())'";

  output DAE.Exp ores;

algorithm
 ores := matchcontinue(inExp1, inExp2, inExp3)
   local
     DAE.Exp e, e1, e2, e3, e4, res;

    case(DAE.IFEXP(e,e1,e2), _,_)
     equation
         false = expHasCref(e, inExp3);
         true = expHasCref(e1, inExp3);
         true = expHasCref(e2, inExp3);
         e3 = expAddX(inExp2, e1, inExp3);
         e4 = expAddX(inExp2, e2, inExp3);

         res = DAE.IFEXP(e, e3, e4);
     then res;
    case(_, DAE.IFEXP(e,e1,e2), _)
     equation
         false = expHasCref(e, inExp3);
         true = expHasCref(e1, inExp3);
         true = expHasCref(e2, inExp3);
         e3 = expAddX(inExp1, e1, inExp3);
         e4 = expAddX(inExp1, e2, inExp3);

         res = DAE.IFEXP(e, e3, e4);
     then res;

     else
      equation
       res = expAddX2(inExp1, inExp2, inExp3);
      then res;

 end matchcontinue;

end expAddX;

protected function expAddX2
"
 helprer function for preprocessingSolve
 a*f(x) + b*f(x) = (a+b)*f(x)
 author: Vitalij Ruge
"
  input DAE.Exp inExp1 "lhs";
  input DAE.Exp inExp2 "rhs";
  input DAE.Exp inExp3 "DAE.CREF or 'der(DAE.CREF())'";

  output DAE.Exp ores;

protected
  list<DAE.Exp> f1, f2;
  DAE.Exp e0,e1,e2;
  DAE.Boolean neg;
  list<DAE.Exp> factorWithX1, factorWithoutX1,  factorWithX2, factorWithoutX2;
  DAE.Exp pWithX1, pWithoutX1, pWithX2, pWithoutX2;

algorithm
  (e0, e1, neg) := match(inExp1)
                   local DAE.Exp ee1, ee2;
                   case(DAE.BINARY(ee1,DAE.ADD(),ee2))
                    then(ee1, ee2, false);
                   case(DAE.BINARY(ee1,DAE.SUB(),ee2))
                    then(ee1, ee2, true);
                   else
                    then(DAE.RCONST(0.0), inExp1, false);
                   end match;

  f1 := Expression.expandFactors(e1);
  (factorWithX1, factorWithoutX1) := List.split1OnTrue(f1, expHasCref, inExp3);
  pWithX1 := makeProductLstSort(factorWithX1);
  pWithoutX1 := makeProductLstSort(factorWithoutX1);

  f2 := Expression.expandFactors(inExp2);
  (factorWithX2, factorWithoutX2) := List.split1OnTrue(f2, expHasCref, inExp3);
  (pWithX2,_) := ExpressionSimplify.simplify1(makeProductLstSort(factorWithX2));
  pWithoutX2 := makeProductLstSort(factorWithoutX2);
  //print("\nf1 =");print(ExpressionDump.printExpListStr(f1));
  //print("\nf2 =");print(ExpressionDump.printExpListStr(f2));

  if Expression.expEqual(pWithX2,pWithX1) then
    // e0 + a*x + b*x -> e0 + (a+b)*x
    if not neg then
      ores := Expression.expAdd(pWithoutX1, pWithoutX2);
    else
    // e0 - a*x + b*x -> e0 + (b-a)*x
      ores := Expression.expSub(pWithoutX2, pWithoutX1);
    end if;
    ores := Expression.expMul(ores, pWithX2);
  elseif Expression.expEqual(pWithX2, Expression.negate(pWithX1)) then
    // e0 + a*(-x) + b*x -> e0 + (b-a)*x
    if not neg then
      ores := Expression.expSub(pWithoutX2, pWithoutX1);
    else
    // e0 - a*(-x) + b*x -> e0 + (b-a)*x
      ores := Expression.expAdd(pWithoutX1, pWithoutX2);
    end if;
    ores := Expression.expMul(ores, pWithX2);
  else
    e1 := Expression.expMul(pWithoutX1, pWithX1);
    e2 := Expression.expMul(pWithoutX2, pWithX2);
    ores := Expression.expAdd(e1,e2);
  end if;

  ores := Expression.expAdd(e0,ores);

end expAddX2;

public function collectX
  input DAE.Exp inExp1 "lhs";
  input DAE.Exp inExp3 "DAE.CREF";
  input DAE.Boolean expand = true;
  output DAE.Exp outLhs;
  output DAE.Exp outRhs;
algorithm
 (outLhs, outRhs) := preprocessingSolve5(inExp1, inExp3, expand);
end collectX;

protected function preprocessingSolve5
"
 helprer function for preprocessingSolve
 split and sort with respect to x
 where x = cref

 f(x,y) = {h(y)*g(x,y), k(y)}

 author: Vitalij Ruge
"
  input DAE.Exp inExp1 "lhs";
  input DAE.Exp inExp3 "DAE.CREF or 'der(DAE.CREF())'";
  input DAE.Boolean expand;
  output DAE.Exp outLhs = DAE.RCONST(0.0);
  output DAE.Exp outRhs;

protected
  DAE.Exp res;
  list<DAE.Exp> lhs, rhs, resTerms;

algorithm

   //can be improve with Expression.getTermsContainingX ???

   if expHasCref(inExp1, inExp3) then
     resTerms := Expression.terms(inExp1);
     // split
     (lhs, rhs) := List.split1OnTrue(resTerms, expHasCref, inExp3);
     //print("\nlhs =");print(ExpressionDump.printExpListStr(lhs));
     //print("\nrhs =");print(ExpressionDump.printExpListStr(rhs));

     // sort
     // a*f(x)*b -> c*f(x)
     for e in lhs loop
       outLhs := expAddX(e, outLhs, inExp3); // special add
     end for;

     //rhs
     outRhs := Expression.makeSum(rhs);
     (outRhs,_) := ExpressionSimplify.simplify1(outRhs);

     if expand then
       resTerms := Expression.terms(Expression.expand(outLhs));
       (lhs, rhs) := List.split1OnTrue(resTerms, expHasCref, inExp3);
       outLhs := DAE.RCONST(0.0);
       // sort
       // a*f(x)*b -> c*f(x)
       for e in lhs loop
         outLhs := expAddX(e, outLhs, inExp3); // special add
       end for;
       //rhs
       outRhs := Expression.expAdd(outRhs,Expression.makeSum(rhs));
       (outRhs,_) := ExpressionSimplify.simplify1(outRhs);

       resTerms := Expression.allTerms(outLhs);
       (lhs, rhs) := List.split1OnTrue(resTerms, expHasCref, inExp3);
       // sort
       // a*f(x)*b -> c*f(x)
       outLhs := DAE.RCONST(0.0);
       for e in lhs loop
         outLhs := expAddX(e, outLhs, inExp3); // special add
       end for;
       //rhs
       outRhs := Expression.expAdd(outRhs,Expression.makeSum(rhs));
       (outRhs,_) := ExpressionSimplify.simplify1(outRhs);

     end if;

   else
    outRhs := inExp1;
   end if;

end preprocessingSolve5;

protected function unifyFunCalls
"
e.g.
 smooth() -> if
 semiLinear() -> if
 author: Vitalij Ruge
"
  input DAE.Exp inExp1 "lhs";
  input DAE.Exp inExp3 "DAE.CREF or 'der(DAE.CREF())'";
  output DAE.Exp oExp;
  output Boolean newX;
algorithm
 (oExp,_) := Expression.traverseExpTopDown(inExp1, unifyFunCallsWork, (inExp3));
 newX := Expression.expEqual(oExp, inExp1);
end unifyFunCalls;

protected function unifyFunCallsWork
  input DAE.Exp inExp;
  input DAE.Exp iT;
  output DAE.Exp outExp;
  output Boolean cont;
  output DAE.Exp oT;
 algorithm
   (outExp,cont,oT) := matchcontinue(inExp, iT)
   local
     DAE.Exp e, e1,e2,e3, X;
     DAE.Type tp;

   case(DAE.CALL(path = Absyn.IDENT(name = "smooth"), expLst = {_, e}),X)
     equation
       true = expHasCref(e, X);
     then (e, true, iT);

   case(DAE.CALL(path = Absyn.IDENT(name = "noEvent"), expLst = {e}),X)
     equation
       true = expHasCref(e, X);
     then (e, true, iT);

   case(DAE.CALL(path = Absyn.IDENT(name = "semiLinear"),expLst = {e1, e2, e3}),_)
     equation
       false = Expression.isZero(e1);
       tp = Expression.typeof(e1);
       e = DAE.IFEXP(DAE.RELATION(e1,DAE.GREATEREQ(tp), Expression.makeConstZero(tp),-1,NONE()),Expression.expMul(e1,e2), Expression.expMul(e1,e3));
     then (e,true, iT);

   // df_der(x) = (x-old(x))/dt
   case(DAE.CALL(path = Absyn.IDENT(name = "$_DF$DER"),expLst = {e1}),X)
     guard expHasCref(e1, X)
     equation
      tp = Expression.typeof(e1);
      e2 = Expression.crefExp(ComponentReference.makeCrefIdent(BackendDAE.symEulerDT, DAE.T_REAL_DEFAULT, {}));
      e3 = Expression.makePureBuiltinCall("$_old", {e1}, tp);
      e3 = Expression.expSub(e1,e3);
      e = Expression.expDiv(e3,e2);
     then (e,true, iT);

   else (inExp, true, iT);
   end matchcontinue;

end unifyFunCallsWork;


protected function solveFunCalls
"
  - inline modelica functions
  - TODO: support annotation inverse
 author: Vitalij Ruge
"
  input DAE.Exp inExp1 "lhs";
  input DAE.Exp inExp3 "DAE.CREF or 'der(DAE.CREF())'";
  input Option<DAE.FunctionTree> functions;
  output DAE.Exp x;
  output Boolean con;
algorithm
  try
    x := Expression.traverseExpTopDown(inExp1, inlineCallX, (inExp3, functions));
	con := Expression.expEqual(x, inExp1);
  else
    x := inExp1;
	con := false;
 end try;
end solveFunCalls;

protected function removeSimpleCalls
"
 helprer function for preprocessingSolve

 solve e.g.
   exp(x) = y
   log(x) = y
"
  input DAE.Exp inExp1 "lhs";
  input DAE.Exp inExp2 "rhs";
  input DAE.Exp inExp3 "DAE.CREF or 'der(DAE.CREF())'";

  output DAE.Exp outLhs;
  output DAE.Exp outRhs;
  output Boolean con "continue";
algorithm
  (outLhs, outRhs, con) := match(inExp1, inExp2, inExp3)
                            case(DAE.CALL(),_,_) then removeSimpleCalls2(inExp1, inExp2, inExp3);
                            else (inExp1, inExp2, false);
                           end match;
end removeSimpleCalls;


protected function removeSimpleCalls2
"
 helprer function for preprocessingSolve

 solve e.g.
   exp(x) = y
   log(x) = y
"
  input DAE.Exp inExp1 "lhs";
  input DAE.Exp inExp2 "rhs";
  input DAE.Exp inExp3 "DAE.CREF or 'der(DAE.CREF())'";

  output DAE.Exp outLhs;
  output DAE.Exp outRhs;
  output Boolean con "continue";
algorithm
  (outLhs, outRhs, con) := matchcontinue (inExp1,inExp2,inExp3)
    local
      DAE.Exp e1, e2, e3;


    //tanh(x) =y -> x = 1/2 * ln((1+y)/(1-y))
    case (DAE.CALL(path = Absyn.IDENT(name = "tanh"),expLst = {e1}),_,_)
       equation
         true = expHasCref(e1, inExp3);
         false = expHasCref(inExp2, inExp3);
         true = not(Expression.isCref(inExp2) or Expression.isConst(inExp2));
         e2 = Expression.expAdd(DAE.RCONST(1.0), inExp2);
         e3 = Expression.expSub(DAE.RCONST(1.0), inExp2);
         e2 = Expression.makeDiv(e2, e3);
         e2 = Expression.makePureBuiltinCall("log",{e2},DAE.T_REAL_DEFAULT);
         e2 = Expression.expMul(DAE.RCONST(0.5), e2);
       then (e1, e2, true);
    // sinh(x) -> ln(y+(sqrt(1+y^2))
    case (DAE.CALL(path = Absyn.IDENT(name = "sinh"),expLst = {e1}),_,_)
      equation
         true = expHasCref(e1, inExp3);
         false = expHasCref(inExp2, inExp3);
         true = not(Expression.isCref(inExp2) or Expression.isConst(inExp2));
         e2 = Expression.expPow(inExp2, DAE.RCONST(2.0));
         e3 = Expression.expAdd(e2,DAE.RCONST(1.0));
         e2 = Expression.makePureBuiltinCall("sqrt",{e3},DAE.T_REAL_DEFAULT);
         e3 = Expression.expAdd(inExp2, e2);
         e2 = Expression.makePureBuiltinCall("log",{e3},DAE.T_REAL_DEFAULT);
      then (e1,e2,true);

    // log10(f(a)) = g(b) => f(a) = 10^(g(b))
    case (DAE.CALL(path = Absyn.IDENT(name = "log10"),expLst = {e1}),_,_)
       equation
         true = expHasCref(e1, inExp3);
         false = expHasCref(inExp2, inExp3);
         e2 = Expression.expPow(DAE.RCONST(10.0), inExp2);
       then (e1, e2, true);
    // log(f(a)) = g(b) => f(a) = exp(g(b))
    case (DAE.CALL(path = Absyn.IDENT(name = "log"),expLst = {e1}),_,_)
       equation
         true = expHasCref(e1, inExp3);
         false = expHasCref(inExp2, inExp3);
         e2 = Expression.makePureBuiltinCall("exp",{inExp2},DAE.T_REAL_DEFAULT);
       then (e1, e2, true);
    // exp(f(a)) = g(b) => f(a) = log(g(b))
    case (DAE.CALL(path = Absyn.IDENT(name = "exp"),expLst = {e1}),_,_)
       equation
         true = expHasCref(e1, inExp3);
         false = expHasCref(inExp2, inExp3);
         e2 = Expression.makePureBuiltinCall("log",{inExp2},DAE.T_REAL_DEFAULT);
       then (e1, e2, true);
    // sqrt(f(a)) = g(b) => f(a) = (g(b))^2
    case (DAE.CALL(path = Absyn.IDENT(name = "sqrt"),expLst = {e1}),_,_)
       equation
         true = expHasCref(e1, inExp3);
         false = expHasCref(inExp2, inExp3);
         e2 = DAE.RCONST(2.0);
         e2 = Expression.expPow(inExp2,e2);
       then (e1, e2, true);
    // semiLinear(0, a, b) = 0 => a = b // rule 1
    case (DAE.CALL(path = Absyn.IDENT(name = "semiLinear"),expLst = {DAE.RCONST(real = 0.0), e1, e2}),DAE.RCONST(real = 0.0),_)
       then (e1,e2,true);
    // smooth(i,f(a)) = rhs -> f(a) = rhs
    case (DAE.CALL(path = Absyn.IDENT(name = "smooth"),expLst = {_, e2}),_,_)
       then (e2, inExp2, true);
    // noEvent(f(a)) = rhs -> f(a) = rhs
    case (DAE.CALL(path = Absyn.IDENT(name = "noEvent"),expLst = {e2}),_,_)
       then (e2, inExp2, true);

    else (inExp1, inExp2, false);
  end matchcontinue;
end removeSimpleCalls2;

protected function inlineCallX
"
inline function call if depends on X where X is cref oder der(cref)
DAE.Exp inExp2 DAE.CREF or 'der(DAE.CREF())'
author: vitalij
"
  input DAE.Exp inExp;
  input tuple<DAE.Exp, Option<DAE.FunctionTree>> iT;
  output DAE.Exp outExp;
  output Boolean cont;
  output tuple<DAE.Exp, Option<DAE.FunctionTree>> oT;
 algorithm
   (outExp,cont,oT) := matchcontinue(inExp, iT)
   local
     DAE.Exp e, X;
     DAE.ComponentRef cr;
     Option<DAE.FunctionTree> functions;
     Boolean b;

   case(DAE.CALL(),(X, functions))
     guard expHasCref(inExp, X)
     equation
       //print("\nIn: ");print(ExpressionDump.printExpStr(inExp));
       (e,((_,_),b,_)) = Inline.forceInlineCall(inExp,((functions,{DAE.NORM_INLINE(),DAE.NO_INLINE()}),false,{}));
       //print("\nOut: ");print(ExpressionDump.printExpStr(e));
     then (e, b, iT);
   else (inExp, true, iT);
   end matchcontinue;
end inlineCallX;

protected function preprocessingSolveTmpVars
"
helper function for solveWork
creat tmp vars if needed!
e.g. for solve abs()

 author: Vitalij Ruge
"
  input DAE.Exp inExp1;
  input DAE.Exp inExp2;
  input DAE.Exp inExp3;
  input Option<Integer> uniqueEqIndex "offset for tmp vars";
  input list<BackendDAE.Equation> ieqnForNewVars;
  input list<DAE.ComponentRef> inewVarsCrefs;
  input Integer idepth;
  output DAE.Exp x;
  output DAE.Exp y;
  output Boolean new_x;
  output list<BackendDAE.Equation> eqnForNewVars "eqn for tmp vars";
  output list<DAE.ComponentRef> newVarsCrefs;
  output Integer odepth;
algorithm
  (x, y, new_x, eqnForNewVars, newVarsCrefs, odepth) := match(uniqueEqIndex)
        local Integer i;
        case(SOME(i)) then preprocessingSolveTmpVarsWork(inExp1, inExp2, inExp3, i, ieqnForNewVars, inewVarsCrefs, idepth);
        else (inExp1, inExp2, false, ieqnForNewVars, inewVarsCrefs, idepth);
        end match;
end preprocessingSolveTmpVars;

protected function preprocessingSolveTmpVarsWork
"
helper function for solveWork
creat tmp vars if needed!
e.g. for solve abs
"
  input DAE.Exp inExp1;
  input DAE.Exp inExp2;
  input DAE.Exp inExp3;
  input Integer uniqueEqIndex "offset for tmp vars";
  input list<BackendDAE.Equation> ieqnForNewVars;
  input list<DAE.ComponentRef> inewVarsCrefs;
  input Integer idepth "depth of tmp var";
  output DAE.Exp x;
  output DAE.Exp y;
  output Boolean new_x;
  output list<BackendDAE.Equation> eqnForNewVars "eqn for tmp vars";
  output list<DAE.ComponentRef> newVarsCrefs;
  output Integer odepth;
algorithm
  (x, y, new_x, eqnForNewVars, newVarsCrefs, odepth) := matchcontinue(inExp1, inExp2)
  local DAE.Exp e1, e_1, e, e2, exP, lhs, e3, e4, e5, e6, rhs, a1,x1, a2,x2, ee1, ee2;
  DAE.Exp acosy, k1, k2;
  tuple<DAE.Exp, DAE.Exp> a, c;
  list<DAE.Exp> z1, z2, z3, z4;
  DAE.ComponentRef cr;
  DAE.Type tp;
  BackendDAE.Equation eqn;
  list<BackendDAE.Equation> eqnForNewVars_;
  list<DAE.ComponentRef> newVarsCrefs_;
  Boolean b, b1, b2, b3;
  DAE.Operator op1, op2;

  //tanh(x) =y -> x = 1/2 * ln((1+y)/(1-y))
  case (DAE.CALL(path = Absyn.IDENT(name = "tanh"),expLst = {e1}),_)
    equation
      true = expHasCref(e1, inExp3);
      false = expHasCref(inExp2, inExp3);
      tp = Expression.typeof(inExp2);
      (e, eqnForNewVars_, newVarsCrefs_) = makeTmpEqnAndCrefFromExp(inExp2, tp, "Y$TANH", uniqueEqIndex, idepth, ieqnForNewVars, inewVarsCrefs,false);
      e2 = Expression.expAdd(DAE.RCONST(1.0), e);
      e3 = Expression.expSub(DAE.RCONST(1.0), e);
      e2 = Expression.makeDiv(e2, e3);
      e2 = Expression.makePureBuiltinCall("log",{e2},DAE.T_REAL_DEFAULT);
      e2 = Expression.expMul(DAE.RCONST(0.5), e2);
     then (e1, e2, true,eqnForNewVars_,newVarsCrefs_,idepth + 1);

  // sinh(x) -> ln(y+(sqrt(1+y^2))
  case (DAE.CALL(path = Absyn.IDENT(name = "sinh"),expLst = {e1}),_)
    equation
      true = expHasCref(e1, inExp3);
      false = expHasCref(inExp2, inExp3);
      tp = Expression.typeof(inExp2);
      (e, eqnForNewVars_, newVarsCrefs_) = makeTmpEqnAndCrefFromExp(inExp2, tp, "Y$SINH", uniqueEqIndex, idepth, ieqnForNewVars, inewVarsCrefs,false);
      e2 = Expression.expPow(e, DAE.RCONST(2.0));
      e3 = Expression.expAdd(e2,DAE.RCONST(1.0));
      e2 = Expression.makePureBuiltinCall("sqrt",{e3},DAE.T_REAL_DEFAULT);
      e3 = Expression.expAdd(e, e2);
      e2 = Expression.makePureBuiltinCall("log",{e3},DAE.T_REAL_DEFAULT);
    then (e1,e2,true,eqnForNewVars_,newVarsCrefs_,idepth + 1);

  // cosh(x) -> ln(y +- (sqrt(y^2 - 1))
  case (DAE.CALL(path = Absyn.IDENT(name = "cosh"),expLst = {e1}),_)
    equation
      true = expHasCref(e1, inExp3);
      false = expHasCref(inExp2, inExp3);

      tp = Expression.typeof(inExp2);
      (rhs, eqnForNewVars_, newVarsCrefs_) = makeTmpEqnAndCrefFromExp(inExp2, tp, "Y$SINH", uniqueEqIndex, idepth, ieqnForNewVars, inewVarsCrefs,false);

      tp = Expression.typeof(e1);
      exP = makeIntialGuess(e1,tp,inExp3,e1);
      (exP, eqnForNewVars_, newVarsCrefs_) = makeTmpEqnAndCrefFromExp(exP, tp, "SIGN$SINH", uniqueEqIndex, idepth, eqnForNewVars_, newVarsCrefs_,false);


      e_1 = Expression.makePureBuiltinCall("$_signNoNull", {exP}, tp);

      e2 = Expression.expPow(rhs, DAE.RCONST(2.0));
      e3 = Expression.expSub(e2, DAE.RCONST(1.0));
      e2 = Expression.makePureBuiltinCall("sqrt",{e3},DAE.T_REAL_DEFAULT);

      e3 = Expression.expAdd(rhs, Expression.expMul(e_1,e2));
      e2 = Expression.makePureBuiltinCall("log",{e3},DAE.T_REAL_DEFAULT);

    then (e1,e2,true,eqnForNewVars_,newVarsCrefs_,idepth + 1);

  // cos(y) = x -> y = acos(x) + 2*pi*k
  case (DAE.CALL(path = Absyn.IDENT(name = "cos"),expLst = {e1}),_)
  equation
    true = expHasCref(e1, inExp3);
    false = expHasCref(inExp2, inExp3);

    tp = Expression.typeof(inExp2);
    (rhs, eqnForNewVars_, newVarsCrefs_) = makeTmpEqnAndCrefFromExp(inExp2, tp, "Y$COS", uniqueEqIndex, idepth, ieqnForNewVars, inewVarsCrefs,false);

    acosy = Expression.makePureBuiltinCall("acos", {rhs}, tp);
    (acosy, eqnForNewVars_, newVarsCrefs_) = makeTmpEqnAndCrefFromExp(acosy, tp, "ACOS$COS", uniqueEqIndex, idepth, eqnForNewVars_, newVarsCrefs_,false);

    exP = makeIntialGuess(e1,tp,inExp3,e1);
    (exP, eqnForNewVars_, newVarsCrefs_) = makeTmpEqnAndCrefFromExp(exP, tp, "PREX$COS", uniqueEqIndex, idepth, eqnForNewVars_, newVarsCrefs_, false);

    k1 = helpInvCos(acosy, exP, tp, true);
    k2 = helpInvCos(acosy, exP, tp, false);
    (k1, eqnForNewVars_, newVarsCrefs_) = makeTmpEqnAndCrefFromExp(k1, tp, "k1$COS", uniqueEqIndex, idepth, eqnForNewVars_, newVarsCrefs_, false);
    (k2, eqnForNewVars_, newVarsCrefs_) = makeTmpEqnAndCrefFromExp(k2, tp, "k2$COS", uniqueEqIndex, idepth, eqnForNewVars_, newVarsCrefs_, false);

    x1 = helpInvCos2(k1, acosy, tp ,true);
    x2 = helpInvCos2(k2, acosy, tp ,false);
    (x1, eqnForNewVars_, newVarsCrefs_) = makeTmpEqnAndCrefFromExp(x1, tp, "x1$COS", uniqueEqIndex, idepth, eqnForNewVars_, newVarsCrefs_, false);
    (x2, eqnForNewVars_, newVarsCrefs_) = makeTmpEqnAndCrefFromExp(x2, tp, "x2$COS", uniqueEqIndex, idepth, eqnForNewVars_, newVarsCrefs_, false);

    rhs = helpInvCos3(x1,x2,exP,tp);

  then(e1, rhs, true, eqnForNewVars_, newVarsCrefs_, idepth + 1);


  // sin(y) = x -> y = asin(x) + 2*pi*k
  //                 = -asin(x) + pi*(2*k+1)
  case (DAE.CALL(path = Absyn.IDENT(name = "sin"),expLst = {e1}),_)
  equation
    true = expHasCref(e1, inExp3);
    false = expHasCref(inExp2, inExp3);

    tp = Expression.typeof(inExp2);
    (rhs, eqnForNewVars_, newVarsCrefs_) = makeTmpEqnAndCrefFromExp(inExp2, tp, "Y$SIN", uniqueEqIndex, idepth, ieqnForNewVars, inewVarsCrefs,false);

    acosy = Expression.makePureBuiltinCall("asin", {rhs}, tp);
    (acosy, eqnForNewVars_, newVarsCrefs_) = makeTmpEqnAndCrefFromExp(acosy, tp, "ASIN$SIN", uniqueEqIndex, idepth, eqnForNewVars_, newVarsCrefs_,false);

    exP = makeIntialGuess(e1,tp,inExp3,e1);
    (exP, eqnForNewVars_, newVarsCrefs_) = makeTmpEqnAndCrefFromExp(exP, tp, "PREX$SIN", uniqueEqIndex, idepth, eqnForNewVars_, newVarsCrefs_, false);

    k1 = helpInvSin(acosy, e1, tp, true);
    k2 = helpInvSin(acosy, e1, tp, false);
    (k1, eqnForNewVars_, newVarsCrefs_) = makeTmpEqnAndCrefFromExp(k1, tp, "k1$SIN", uniqueEqIndex, idepth, eqnForNewVars_, newVarsCrefs_, false);
    (k2, eqnForNewVars_, newVarsCrefs_) = makeTmpEqnAndCrefFromExp(k2, tp, "k2$SIN", uniqueEqIndex, idepth, eqnForNewVars_, newVarsCrefs_, false);

    x1 = helpInvSin2(k1, acosy, tp ,true);
    x2 = helpInvSin2(k2, acosy, tp ,false);
    (x1, eqnForNewVars_, newVarsCrefs_) = makeTmpEqnAndCrefFromExp(x1, tp, "x1$SIN", uniqueEqIndex, idepth, eqnForNewVars_, newVarsCrefs_, false);
    (x2, eqnForNewVars_, newVarsCrefs_) = makeTmpEqnAndCrefFromExp(x2, tp, "x2$SIN", uniqueEqIndex, idepth, eqnForNewVars_, newVarsCrefs_, false);

    rhs = helpInvCos3(x1,x2,exP,tp);

  then(e1, rhs, true, eqnForNewVars_, newVarsCrefs_, idepth + 1);

  // tan(x) = y -> x = atan(y) + k*pi
  case (DAE.CALL(path = Absyn.IDENT(name = "tan"),expLst = {e1}),_)
  equation
    true = expHasCref(e1, inExp3);
    false = expHasCref(inExp2, inExp3);

    tp = Expression.typeof(inExp2);
    (rhs, eqnForNewVars_, newVarsCrefs_) = makeTmpEqnAndCrefFromExp(inExp2, tp, "Y$TAN", uniqueEqIndex, idepth, ieqnForNewVars, inewVarsCrefs,false);

    acosy = Expression.makePureBuiltinCall("atan", {rhs}, tp);
    (acosy, eqnForNewVars_, newVarsCrefs_) = makeTmpEqnAndCrefFromExp(acosy, tp, "ATAN$TAN", uniqueEqIndex, idepth, eqnForNewVars_, newVarsCrefs_,false);

    exP = makeIntialGuess(e1,tp,inExp3,e1);
    (exP, eqnForNewVars_, newVarsCrefs_) = makeTmpEqnAndCrefFromExp(exP, tp, "PREX$TAN", uniqueEqIndex, idepth, eqnForNewVars_, newVarsCrefs_, false);
    e = DAE.RCONST(3.1415926535897932384626433832795028841971693993751058);

    k1 = Expression.expSub(exP, acosy);
    k1 = Expression.makeDiv(k1,e);
    k1 = Expression.makePureBuiltinCall("$_round",{k1},tp);

    rhs = Expression.expMul(k1,e);
    rhs = Expression.expAdd(acosy, rhs);

  then(e1, rhs, true, eqnForNewVars_, newVarsCrefs_, idepth + 1);

  // abs(f(x)) = g(y) -> f(x) = sign(f(x))*g(y)
  case(DAE.CALL(path = Absyn.IDENT(name = "abs"),expLst = {e1}), _)
  equation
    true = expHasCref(e1, inExp3);
    false = expHasCref(inExp2, inExp3);

    tp = Expression.typeof(e1);
    exP = makeIntialGuess(e1,tp,inExp3,e1);
    (exP, eqnForNewVars_, newVarsCrefs_) = makeTmpEqnAndCrefFromExp(exP, tp, "X$ABS", uniqueEqIndex, idepth, ieqnForNewVars, inewVarsCrefs, false);
    e_1 = Expression.makePureBuiltinCall("$_signNoNull", {exP}, tp);
    lhs = Expression.expMul(e_1, inExp2);

  then(e1, lhs, true, eqnForNewVars_, newVarsCrefs_, idepth + 1);

  // x^n = y -> x = y^(1/n)
  case(DAE.BINARY(e1, DAE.POW(tp), e2),_)
  equation
    true = expHasCref(e1, inExp3);
    false = expHasCref(e2, inExp3);
    tp = Expression.typeof(e1);
    exP = makeIntialGuess(e1,tp,inExp3,e1);
    (exP, eqnForNewVars_, newVarsCrefs_) = makeTmpEqnAndCrefFromExp(exP, tp, "X$ABS", uniqueEqIndex, idepth, ieqnForNewVars, inewVarsCrefs, false);
    e_1 = Expression.makePureBuiltinCall("$_signNoNull", {exP}, tp);
    lhs = Expression.expPow(inExp2,Expression.inverseFactors(e2));
    lhs = Expression.makePureBuiltinCall("abs", {lhs}, tp);
    lhs = Expression.expMul(e_1,lhs);

  then(e1, lhs, true, eqnForNewVars_, newVarsCrefs_, idepth + 1);

  // $_DF$DER(x) =y -> (x-old(x))/dt = y -> x = y*dt + old(x)
  case(DAE.CALL(path = Absyn.IDENT(name = "$_DF$DER"),expLst = {e1}), _)
  equation
    true = expHasCref(e1, inExp3);
    false = expHasCref(inExp2, inExp3);
    tp = Expression.typeof(e1);
    e2 = Expression.crefExp(ComponentReference.makeCrefIdent(BackendDAE.symEulerDT, DAE.T_REAL_DEFAULT, {}));
    lhs = Expression.makePureBuiltinCall("$_old", {e1}, tp);
    lhs = Expression.expAdd(Expression.expMul(inExp2,e2), lhs);
  then(e1, lhs, true, ieqnForNewVars, inewVarsCrefs, idepth + 1);


  //QE
  // a*x^n + b*x^m = c
  // a*x^n - b*x^m = c
  case(DAE.BINARY(ee1, op1, ee2),_)
  guard(Expression.isAddOrSub(op1))
  equation
    (z1, z2) = List.split1OnTrue(Expression.factors(ee1), expHasCref, inExp3);
    (z3, z4) = List.split1OnTrue(Expression.factors(ee2), expHasCref, inExp3);

    x1 = makeProductLstSort(z1);
    a1 = makeProductLstSort(z2);

    x2 = makeProductLstSort(z3);
    a2 = if Expression.isAdd(op1) then makeProductLstSort(z4) else  Expression.negate(makeProductLstSort(z4));
/*
    print("\nx1 = ");print(ExpressionDump.printExpStr(x1));
    print("\nx2 = ");print(ExpressionDump.printExpStr(x2));
    print("\na1 = ");print(ExpressionDump.printExpStr(a1));
    print("\na2 = ");print(ExpressionDump.printExpStr(a2));
*/
    a = simplifyBinaryMulCoeff(x1);
    c = simplifyBinaryMulCoeff(x2);
    (e2 ,e3) = a;
    (e5, e6) = c;
    (lhs, rhs, eqnForNewVars_, newVarsCrefs_) = solveQE(a1,e2,e3,a2,e5,e6,inExp2,inExp3,ieqnForNewVars,inewVarsCrefs,uniqueEqIndex,idepth);
  then(lhs, rhs, true, eqnForNewVars_, newVarsCrefs_, idepth + 1);

  else (inExp1, inExp2, false, ieqnForNewVars, inewVarsCrefs, idepth);

  end matchcontinue;

end preprocessingSolveTmpVarsWork;

protected function simplifyBinaryMulCoeff
"generalization of ExpressionSimplify.simplifyBinaryMulCoeff2"
  input DAE.Exp inExp;
  output tuple<DAE.Exp, DAE.Exp> outRes;
algorithm
  outRes := match(inExp)
    local
      DAE.Exp e,e1,e2;
      DAE.Exp coeff;

    case ((e as DAE.CREF()))
      then ((e, DAE.RCONST(1.0)));

    case (DAE.BINARY(exp1 = e1,operator = DAE.POW(),exp2 = DAE.UNARY(operator = DAE.UMINUS(), exp = coeff)))
      then
        ((e1, Expression.negate(coeff)));

    case (DAE.BINARY(exp1 = e1,operator = DAE.POW(),exp2 = coeff))
      then ((e1,coeff));

    case (DAE.BINARY(exp1 = e1,operator = DAE.MUL(),exp2 = e2))
    guard(Expression.expEqual(e1, e2))
      then
        ((e1, DAE.RCONST(2.0)));

    case(DAE.BINARY(e1, DAE.DIV(), e2))
    guard(Expression.isOne(e1))
      then(e2, DAE.RCONST(-1.0));

    case(DAE.CALL(path=Absyn.IDENT("sqrt"),expLst={e}))
      then ((e,DAE.RCONST(0.5)));

    else ((inExp,DAE.RCONST(1.0)));

  end match;
end simplifyBinaryMulCoeff;

protected function solveQE
"
solve Quadratic equation with respect to inExp3
IN: a,x,n,b,y,m
where solve(a*x^n + b*y^m = inExp2) with 2*m = n or 2*n = m and y = x

author: Vitalij Ruge
"
 input DAE.Exp e1,e2,e3,e4,e5,e6;
 input DAE.Exp inExp2;
 input DAE.Exp inExp3;

 input list<BackendDAE.Equation> ieqnForNewVars "eqn for tmp vars";
 input list<DAE.ComponentRef> inewVarsCrefs "cref for tmp vars";
 input Integer uniqueEqIndex, idepth "need for tmp vars";

 output DAE.Exp rhs, lhs;
 output list<BackendDAE.Equation> eqnForNewVars;
 output list<DAE.ComponentRef> newVarsCrefs;

protected
  DAE.Exp e, e7, con, invExp, x1, x2, x, exP;
  DAE.Exp a,b,c, n, sgnb, b2, ac, sExp1, sExp2;
  DAE.ComponentRef cr;
  DAE.Type tp;
  BackendDAE.Equation eqn;
  Boolean b1, b3;
algorithm
    false := Expression.isZero(e1) and Expression.isZero(e2);
    true := Expression.expEqual(e2,e5);
    b1 := Expression.expEqual(e3, Expression.expMul(DAE.RCONST(2.0),e6));
    b3 := Expression.expEqual(e6, Expression.expMul(DAE.RCONST(2.0),e3));

    true := b1 or b3;
    false := expHasCref(e1, inExp3);
    true := expHasCref(e2, inExp3);
    false := expHasCref(e3, inExp3);
    false := expHasCref(e4, inExp3);
    true := expHasCref(e5, inExp3);
    false := expHasCref(e6, inExp3);
    false := expHasCref(inExp2, inExp3);


    a := if b1 then e1 else e4;
    b := if b1 then e4 else e1;
    c := Expression.negate(inExp2);
    n := if b1 then e6 else e3;

    tp := Expression.typeof(a);
    (a, eqnForNewVars, newVarsCrefs) := makeTmpEqnAndCrefFromExp(a, tp, "a$QE", uniqueEqIndex, idepth, ieqnForNewVars, inewVarsCrefs, false);
    con := DAE.RELATION(a,DAE.EQUAL(tp),DAE.RCONST(0.0),-1,NONE());

    tp := Expression.typeof(b);
    (b, eqnForNewVars, newVarsCrefs) := makeTmpEqnAndCrefFromExp(b, tp, "b$QE", uniqueEqIndex, idepth, eqnForNewVars, newVarsCrefs, false);
    sgnb := Expression.makePureBuiltinCall("$_signNoNull",{b},tp);
    b2 := Expression.expPow(b, DAE.RCONST(2.0));
    (b2, eqnForNewVars, newVarsCrefs) := makeTmpEqnAndCrefFromExp(b2, tp, "bPow2$QE", uniqueEqIndex, idepth, eqnForNewVars, newVarsCrefs, false);

    tp := Expression.typeof(c);
    (c, eqnForNewVars, newVarsCrefs) := makeTmpEqnAndCrefFromExp(c, tp, "c$QE", uniqueEqIndex, idepth, eqnForNewVars, newVarsCrefs, false);
    ac := Expression.expMul(a,c);
    ac := Expression.expMul(DAE.RCONST(4.0),ac);

    sExp1 := Expression.expSub(b2,ac);
    sExp2 := Expression.makePureBuiltinCall("sqrt",{sExp1},tp);
    sExp2 := Expression.expMul(sgnb, sExp2);


    a := DAE.IFEXP(con, Expression.makeConstOne(tp), a);
    (a, eqnForNewVars, newVarsCrefs) := makeTmpEqnAndCrefFromExp(a, tp, "a1$QE", uniqueEqIndex, idepth, eqnForNewVars, newVarsCrefs, false);

    x1 := Expression.expAdd(b, sExp2);
    x1 := Expression.makeDiv(x1, a);
    x1 := Expression.expMul(DAE.RCONST(-0.5), x1);
    tp := Expression.typeof(x1);
    x1 := DAE.IFEXP(con, Expression.makeConstOne(tp), x1);
    (x1, eqnForNewVars, newVarsCrefs) := makeTmpEqnAndCrefFromExp(x1, tp, "x1$QE", uniqueEqIndex, idepth, eqnForNewVars, newVarsCrefs, false);

    //Vieta
    x2 := Expression.expMul(a,x1);
    x2 := Expression.makeDiv(c,x2);
    x2 := DAE.IFEXP(con, Expression.makeConstOne(tp), x2);
    x2 := DAE.IFEXP(DAE.RELATION(x1,DAE.EQUAL(tp),DAE.RCONST(0.0),-1,NONE()), DAE.RCONST(0.0), x2);
    (x2, eqnForNewVars, newVarsCrefs) := makeTmpEqnAndCrefFromExp(x2, tp, "x2$QE", uniqueEqIndex, idepth, eqnForNewVars, newVarsCrefs, false);

    tp := Expression.typeof(e2);
    exP := makeIntialGuess(e2,tp,inExp3,e2);
    (exP, eqnForNewVars, newVarsCrefs) := makeTmpEqnAndCrefFromExp(exP, tp, "prex$QE", uniqueEqIndex, idepth, eqnForNewVars, newVarsCrefs, false);

    x := helpInvCos3(x1,x2,exP,tp);
    (x, eqnForNewVars, newVarsCrefs) := makeTmpEqnAndCrefFromExp(x, tp, "x$QE", uniqueEqIndex, idepth, eqnForNewVars, newVarsCrefs, false);

    // a = 0
    e7 :=  Expression.makeDiv(inExp2,b);
    invExp := Expression.inverseFactors(n);
    (invExp, _) :=  ExpressionSimplify.simplify1(invExp);
    e7 := Expression.expPow(e7, invExp);

    // if a==0
    rhs := DAE.IFEXP(con, e7 , x);
    // lhs
    lhs := if b1 then Expression.expPow(e2, e6) else Expression.expPow(e2, e3);

end solveQE;

protected function solveIfExp
"
 solve:
  if(f(y), f(x), g(x) ) = h(y) w.r.t. x
"
  input DAE.Exp inExp1;
  input DAE.Exp inExp2;
  input DAE.Exp inExp3;
  input Option<DAE.FunctionTree> functions;
  input Option<Integer> uniqueEqIndex "offset for tmp vars";
  input Integer idepth;
  output DAE.Exp outExp;
  output list<DAE.Statement> outAsserts;
  output list<BackendDAE.Equation> eqnForNewVars "eqn for tmp vars";
  output list<DAE.ComponentRef> newVarsCrefs;
  output Integer odepth;

algorithm
   (outExp,outAsserts,eqnForNewVars,newVarsCrefs,odepth) := match(inExp1,inExp2,inExp3, functions, uniqueEqIndex)
   local
      DAE.Exp e1,e2,e3,res,lhs,rhs;
      list<DAE.Statement> asserts,asserts1,asserts2;
      list<BackendDAE.Equation> eqns, eqns1;
      list<DAE.ComponentRef> var, var1;
      Integer depth;

      //  f(a) if(g(b)) then f1(a) else f2(a) =>
      //  a1 = solve(f(a),f1(a)) for a
      //  a2 = solve(f(a),f2(a)) for a
      //  => a = if g(b) then a1 else a2
      case (DAE.IFEXP(e1,e2,e3),_,_,_,_)
        equation
          false = expHasCref(e1, inExp3);

          (lhs, asserts1, eqns, var, depth) = solveWork(e2, inExp2, inExp3, functions, uniqueEqIndex, idepth);
          (rhs,_, eqns1, var1, depth) = solveWork(e3, inExp2, inExp3, functions, uniqueEqIndex, depth);

          res = DAE.IFEXP(e1,lhs,rhs);
          asserts = listAppend(asserts1,asserts1);
      then
        (res,asserts,List.appendNoCopy(eqns1,eqns),  List.appendNoCopy(var1, var), depth);
      else fail();
   end match;

end solveIfExp;

protected function solveLinearSystem
"
 solve linear system with newton step

 ToDo:
  fixed is for ./simulation/modelica/equations/deriveToLog.mos
"
  input DAE.Exp inExp1;
  input DAE.Exp inExp2;
  input DAE.Exp inExp3;
  input Option<DAE.FunctionTree> functions;
  input Integer idepth;
  output DAE.Exp outExp;
  output list<DAE.Statement> outAsserts;
  output list<BackendDAE.Equation> eqnForNewVars = {} "eqn for tmp vars";
  output list<DAE.ComponentRef> newVarsCrefs = {};
  output Integer odepth = idepth;


algorithm
   (outExp,outAsserts) := match(inExp1,inExp2,inExp3)
   local
      DAE.Exp dere,e,z;
      DAE.ComponentRef cr;
      DAE.Exp rhs;
      DAE.Type tp;

    // cr = (e1-e2)/(der(e1-e2,cr))
    case (_,_,DAE.CREF(componentRef = cr))
      equation
        false = hasOnlyFactors(inExp1,inExp2);
        e = Expression.makeDiff(inExp1,inExp2);
        (e,_) = ExpressionSimplify.simplify1(e);
        //print("\n\ne: ");print(ExpressionDump.printExpStr(e));
        dere = Differentiate.differentiateExpSolve(e, cr, functions);
        //print("\nder(e): ");print(ExpressionDump.printExpStr(dere));
        (dere,_) = ExpressionSimplify.simplify(dere);
        false = Expression.isZero(dere);
        false = Expression.expHasCrefNoPreOrStart(dere, cr);
        tp = Expression.typeof(inExp3);
        (z,_) = Expression.makeZeroExpression(Expression.arrayDimension(tp));
        ((e,_)) = Expression.replaceExp(e, inExp3, z);
        (e,_) = ExpressionSimplify.simplify(e);
        rhs = Expression.negate(Expression.makeDiv(e,dere));
      then
        (rhs,{});

      else fail();
   end match;

end solveLinearSystem;

protected function hasOnlyFactors "help function to solve2, returns true if equation e1 == e2, has either e1 == 0 or e2 == 0 and the expression only contains
factors, e.g. a*b*c = 0. In this case we can not solve the equation"
  input DAE.Exp e1;
  input DAE.Exp e2;
  output Boolean res;
algorithm
  res := matchcontinue(e1,e2)

    // try normal
    case(_,_)
      equation
        true = Expression.isZero(e1);
        // More than two factors
        _::_::_ = Expression.factors(e2);
        //.. and more than two crefs
        _::_::_ = Expression.extractCrefsFromExp(e2);
      then
        true;

    // swapped args
    case(_,_)
      equation
        true = Expression.isZero(e2);
        _::_::_ = Expression.factors(e1);
        _::_::_ = Expression.extractCrefsFromExp(e1);
      then
        true;

    else false;

  end matchcontinue;
end hasOnlyFactors;


protected function expHasCref
"
helper function for solve.
case distinction for
DAE.CREF or 'der(DAE.CREF())'
Expression.expHasCrefNoPreOrStart
or
Expression.expHasDerCref
"
  input DAE.Exp inExp1;
  input DAE.Exp inExp3 "DAE.CREF or 'der(DAE.CREF())'";
  output DAE.Boolean res;

algorithm
  res := match(inExp1, inExp3)
         local DAE.ComponentRef cr;

          case(_, DAE.CREF(componentRef = cr)) then Expression.expHasCrefNoPreOrStart(inExp1, cr);
          case(_, DAE.CALL(path = Absyn.IDENT(name = "der"),expLst = {DAE.CREF(componentRef = cr)})) then Expression.expHasDerCref(inExp1, cr);
          else
           equation
            if Flags.isSet(Flags.FAILTRACE) then
              print("\n-ExpressionSolve.solve failed:");
              print(" with respect to: ");print(ExpressionDump.printExpStr(inExp3));
              print(" not support!");
              print("\n");
            end if;
          then fail();
         end match;

end expHasCref;

protected function makeProductLstSort
 "Takes a list of expressions an makes a product
  expression multiplying all elements in the list.

- a*if(b,c,d) -> if(b,a*c,a*d)

"
  input list<DAE.Exp> inExpLst;
  output DAE.Exp outExp;
protected
  DAE.Type tp;
  list<DAE.Exp> expLstDiv, expLst, expLst2;
  DAE.Exp e, e1, e2;
  DAE.Operator op;
algorithm
  if listEmpty(inExpLst) then
    outExp := DAE.RCONST(1.0);
  return;
  end if;

  tp := Expression.typeof(listHead(inExpLst));

  (expLstDiv, expLst) :=  List.splitOnTrue(inExpLst, Expression.isDivBinary);
  outExp := makeProductLstSort2(expLst, tp);
  if not listEmpty(expLstDiv) then
    expLst2 := {};
    expLst := {};

    for elem in expLstDiv loop
      DAE.BINARY(e1,op,e2) := elem;
      expLst := e1::expLst;
      expLst2 := e2::expLst2;
    end for;

    if not listEmpty(expLst2) then
      e := makeProductLstSort(expLst2);
      if not Expression.isOne(e) then
        outExp := Expression.makeDiv(outExp,e);
      end if;
    end if;

    if not listEmpty(expLst) then
      e := makeProductLstSort(expLst);
      outExp := Expression.expMul(outExp,e);
    end if;

  end if;

end makeProductLstSort;


protected function makeProductLstSort2
  input list<DAE.Exp> inExpLst;
  input DAE.Type tp;
  output DAE.Exp outExp = Expression.makeConstOne(tp);
protected
  list<DAE.Exp> rest;
algorithm
  rest := ExpressionSimplify.simplifyList(inExpLst, {});
  for elem in rest loop
    if not Expression.isOne(elem) then
    outExp := match(elem)
              local DAE.Exp e1,e2,e3;
              case(DAE.IFEXP(e1,e2,e3))
              then DAE.IFEXP(e1, Expression.expMul(outExp,e2), Expression.expMul(outExp,e3));
              else Expression.expMul(outExp, elem);
              end match;
    end if;
  end for;

end makeProductLstSort2;

protected function makeTmpEqnAndCrefFromExp
  input DAE.Exp iExp;
  input DAE.Type tp;
  input String name;
  input Integer index1, index2;
  input list<BackendDAE.Equation> ieqnForNewVars;
  input list<DAE.ComponentRef> inewVarsCrefs;
  input Boolean need;
  output DAE.Exp oExp;
  output list<BackendDAE.Equation> oeqnForNewVars;
  output list<DAE.ComponentRef> onewVarsCrefs;
protected
  DAE.ComponentRef cr = ComponentReference.makeCrefIdent("$TMP$VAR$" + intString(index1) + "$" + intString(index2) + name, tp , {});
  BackendDAE.Equation eqn;
algorithm
  (oExp,_) := ExpressionSimplify.simplify1(iExp);
  if need or not (Expression.isCref(oExp) or Expression.isConstValue(oExp)) then
    eqn := BackendDAE.SOLVED_EQUATION(cr, oExp, DAE.emptyElementSource, BackendDAE.EQ_ATTR_DEFAULT_UNKNOWN);
    oExp := Expression.crefExp(cr);
    oeqnForNewVars := eqn::ieqnForNewVars;
    onewVarsCrefs := cr :: inewVarsCrefs;
  else
    oeqnForNewVars := ieqnForNewVars;
    onewVarsCrefs := inewVarsCrefs;
  end if;
end makeTmpEqnAndCrefFromExp;

protected function makeIntialGuess
  input DAE.Exp iExp;
  input DAE.Type tp;
  input DAE.Exp iExp3;
  input DAE.Exp iExp2;
  output DAE.Exp oExp;
protected
  DAE.Exp con, e;
algorithm
 con := Expression.makePureBuiltinCall("initial",{},tp);
 (e,_) := Expression.traverseExpBottomUp(iExp2,makeIntialGuess2,(iExp3, "$_start",tp,true));
 (oExp,_) := Expression.traverseExpBottomUp(iExp2,makeIntialGuess2,(iExp3, "$_initialGuess",tp,false));
 oExp := DAE.IFEXP(con,e,oExp);
end makeIntialGuess;

protected function makeIntialGuess2
  input DAE.Exp iExp;
  input tuple<DAE.Exp, String, DAE.Type, Boolean> itpl;
  output DAE.Exp oExp;
  output tuple<DAE.Exp, String, DAE.Type, Boolean> otpl = itpl;
algorithm
 oExp := match(iExp, itpl)
         local DAE.ComponentRef cr1,cr2;
               DAE.Type tp;
               String fun;
               DAE.Exp e;

         case(DAE.CREF(componentRef = cr1), (DAE.CREF(componentRef = cr2), fun, tp,_))
           guard(ComponentReference.crefEqual(cr1, cr2))
           then Expression.makePureBuiltinCall(fun,{iExp},tp);
         case(_,(_,_,tp,true))
           algorithm
             try
               SOME(e) := makeIntialGuess3(iExp, tp);
             else
               e := iExp;
             end try;
             then e;
         else iExp;
         end match;

end makeIntialGuess2;

protected function makeIntialGuess3
  input DAE.Exp iExp;
  input DAE.Type tp;
  output Option<DAE.Exp> oExp;
algorithm
  oExp := match(iExp)
          local DAE.Exp e, con, o;

          case(DAE.CALL(path = Absyn.IDENT(name = "log"), expLst={e}))
          equation
            con =  DAE.RELATION(e, DAE.LESSEQ(tp), DAE.RCONST(0.0), -1, NONE());
            o = DAE.IFEXP(con, DAE.RCONST(-1/0.000000001), iExp);
          then SOME(o);

          case(DAE.CALL(path = Absyn.IDENT(name = "log10"), expLst={e}))
          equation
            con =  DAE.RELATION(e, DAE.LESSEQ(tp), DAE.RCONST(0.0), -1, NONE());
            o = DAE.IFEXP(con, DAE.RCONST(-1/0.000000001), iExp);
          then SOME(o);

          case(DAE.CALL(path = Absyn.IDENT(name = "sqrt"), expLst={e}))
          equation
            con =  DAE.RELATION(e, DAE.LESSEQ(tp), DAE.RCONST(0.0), -1, NONE());
            o = DAE.IFEXP(con, DAE.RCONST(0.0), iExp);
          then SOME(o);

          case(DAE.BINARY(exp2=e))
          equation
            con =  DAE.RELATION(e, DAE.EQUAL(tp), DAE.RCONST(0.0), -1, NONE());
            o = DAE.IFEXP(con, DAE.RCONST(1.0), iExp);
          then SOME(o);

          else NONE();

         end match;

end makeIntialGuess3;

protected function helpInvCos
  input DAE.Exp acosy;
  input DAE.Exp x;
  input DAE.Type tp;
  input Boolean neg;
  output DAE.Exp k;
protected
  DAE.Exp pi2 = DAE.RCONST(6.283185307179586476925286766559005768394338798750211641949889);
algorithm
  k := if neg then
         Expression.expAdd(x,acosy)
       else
         Expression.expSub(x,acosy);
  k := Expression.makeDiv(k, pi2);
  k := Expression.makePureBuiltinCall("$_round",{k},tp);

end helpInvCos;

protected function helpInvSin
  input DAE.Exp asiny;
  input DAE.Exp x;
  input DAE.Type tp;
  input Boolean neg;
  output DAE.Exp k;
protected
  DAE.Exp pi2 = DAE.RCONST(6.283185307179586476925286766559005768394338798750211641949889);
algorithm
  k := if neg then
         Expression.expAdd(x,asiny)
       else
         Expression.expSub(x,asiny);
  k := Expression.makeDiv(k, pi2);
  if neg then
    k := Expression.expSub(k, DAE.RCONST(0.5));
  end if;
  k := Expression.makePureBuiltinCall("$_round",{k},tp);
end helpInvSin;

protected function helpInvCos2
  input DAE.Exp k;
  input DAE.Exp acosy;
  input DAE.Type tp;
  input Boolean neg;
  output DAE.Exp x;
protected
  DAE.Exp pi2 = DAE.RCONST(6.283185307179586476925286766559005768394338798750211641949889);
algorithm

  x := if neg then Expression.negate(acosy) else acosy;
  x := Expression.expAdd(x, Expression.expMul(k,pi2));

end helpInvCos2;

protected function helpInvSin2
  input DAE.Exp k;
  input DAE.Exp asiny;
  input DAE.Type tp;
  input Boolean neg;
  output DAE.Exp x;
protected
  DAE.Exp pi2 = DAE.RCONST(6.283185307179586476925286766559005768394338798750211641949889);
  DAE.Exp p = DAE.RCONST(3.1415926535897932384626433832795028841971693993751058);
  DAE.Exp e;
algorithm

  x := if neg then Expression.negate(asiny) else asiny;
  e := if neg then Expression.expAdd(Expression.expMul(k,pi2), p) else Expression.expMul(k,pi2);
  x := Expression.expAdd(x, e);

end helpInvSin2;

protected function helpInvCos3
  input DAE.Exp x1;
  input DAE.Exp x2;
  input DAE.Exp x;
  input DAE.Type tp;
  output DAE.Exp y;
protected
  DAE.Exp diffx1 = absDiff(x1,x,tp);
  DAE.Exp diffx2 = absDiff(x2,x,tp);
  DAE.Exp con = DAE.RELATION(diffx1, DAE.LESS(tp), diffx2, -1, NONE());
algorithm
  con := Expression.makeNoEvent(con);
  y := DAE.IFEXP(con, x1, x2);
end helpInvCos3;

protected function absDiff
  input DAE.Exp x;
  input DAE.Exp y;
  input DAE.Type tp;
  output DAE.Exp z;
algorithm
  z := Expression.expSub(x,y);
  z := Expression.makePureBuiltinCall("abs",{z},tp);
end absDiff;

annotation(__OpenModelica_Interface="backend");
end ExpressionSolve;
