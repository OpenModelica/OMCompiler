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

encapsulated package NFInst
" file:        NFInst.mo
  package:     NFInst
  description: Instantiation

  New instantiation, enable with +d=newInst.
"

import Absyn;
import SCode;

import Builtin = NFBuiltin;
import NFBinding.Binding;
import NFComponent.Component;
import NFComponentNode.ComponentNode;
import NFDimension.Dimension;
import NFInstance.ClassTree;
import NFInstance.Instance;
import NFInstNode.InstNode;
import NFInstNode.InstNodeType;
import NFMod.Modifier;
import NFMod.ModifierScope;
import NFEquation.Equation;
import NFStatement.Statement;

protected
import Array;
import Error;
import Flatten = NFFlatten;
import InstUtil = NFInstUtil;
import List;
import Lookup = NFLookup;
import MetaModelica.Dangerous;
import System;
import Typing = NFTyping;

public
function instClassInProgram
  input Absyn.Path classPath;
  input SCode.Program program;
  output DAE.DAElist dae;
protected
  InstNode top, cls;
algorithm
  System.startTimer();

  top := makeTopNode(program);
  cls := Lookup.lookupClassName(classPath, top, Absyn.dummyInfo);
  cls := instantiate(cls, Modifier.NOMOD());

//  // TODO: Why is this a separate phase? Could be done in instComponent?
//  (cls, inst_tree) := instBindings(cls, inst_tree);
//
  cls := Typing.typeClass(cls);

  dae := NFFlatten.flattenClass(cls);

  System.stopTimer();
  //print("NFInst done in " + String(System.getTimerIntervalTime()) + "\n");
end instClassInProgram;

function instantiate
  input output InstNode node;
  input Modifier modifier;
algorithm
  node := partialInstClass(node);
  node := expandClass(node);
  node := instClass(node, modifier);
end instantiate;

function expand
  input output InstNode node;
algorithm
  node := partialInstClass(node);
  node := expandClass(node);
end expand;

function makeTopNode
  input list<SCode.Element> topClasses;
  output InstNode topNode;
protected
  SCode.Element cls;
  ClassTree.Tree scope;
  Instance i;
algorithm
  // Create a fake SCode.Element for the top scope, so we don't have to make the
  // definition in InstNode an option.
  cls := SCode.CLASS("<top>", SCode.defaultPrefixes, SCode.NOT_ENCAPSULATED(),
    SCode.NOT_PARTIAL(), SCode.R_PACKAGE(),
    SCode.PARTS(topClasses, {}, {}, {}, {}, {}, {}, NONE()),
    SCode.COMMENT(NONE(), NONE()), Absyn.dummyInfo);

  // Make an InstNode for the top scope.
  topNode := InstNode.new("<top>", cls, InstNode.EMPTY_NODE(), InstNodeType.TOP_SCOPE());

  // Create a scope from the top classes, and insert them into the top scope instance.
  scope := makeScope(topClasses, topNode);
  i := Instance.initExpandedClass(scope);
  topNode := InstNode.setInstance(i, topNode);
end makeTopNode;

function makeScope
  "Creates a new scope from a list of SCode elements. It returns a scope with
   all the classes added to it, and a list of the non-class elements that were
   not added to the scope."
  input list<SCode.Element> elements;
  input InstNode parentScope;
  output ClassTree.Tree scope "Tree with classes.";
  output list<SCode.Element> componentsExtends = {} "Components and extends.";
protected
  InstNode node;
  list<SCode.Element> imports = {};
algorithm
  scope := ClassTree.new();

  for e in elements loop
    () := match e
      case SCode.CLASS()
        algorithm
          node := InstNode.new(e.name, e, parentScope);
          scope := addClassToScope(e.name, ClassTree.Entry.CLASS(node), e.info, scope);
        then
          ();

      case SCode.COMPONENT()
        algorithm
          componentsExtends := e :: componentsExtends;
        then
          ();

      case SCode.EXTENDS()
        algorithm
          componentsExtends := e :: componentsExtends;
        then
          ();

      case SCode.IMPORT()
        algorithm
          imports := e :: imports;
        then
          ();
    end match;
  end for;

  scope := addImportsToScope(imports, parentScope, scope);
end makeScope;

function addClassToScope
  input String name;
  input ClassTree.Entry id;
  input SourceInfo info;
  input output ClassTree.Tree scope;
algorithm
  try
    scope := ClassTree.add(scope, name, id, ClassTree.addConflictFail);
  else
    // TODO: Add proper error message.
    print("Duplicate element " + name + " found.\n");
    fail();
  end try;
end addClassToScope;

function addImportsToScope
  input list<SCode.Element> imports;
  input InstNode currentScope;
  input output ClassTree.Tree scope;
protected
  Absyn.Import i;
  InstNode node, top_scope;
  SourceInfo info;
algorithm
  if listEmpty(imports) then
    return;
  end if;

  // All imports are looked up from the top scope, so we might as well look it
  // up now to avoid having to do that for each import.
  top_scope := InstNode.topScope(currentScope);

  for imp in imports loop
    SCode.IMPORT(imp = i, info = info) := imp;

    () := match i
      case Absyn.NAMED_IMPORT()
        algorithm
          node := Lookup.lookupClassName(Absyn.FULLYQUALIFIED(i.path), top_scope, info);
          scope := addClassToScope(i.name, ClassTree.Entry.CLASS(node), info, scope);
        then
          ();

      case Absyn.QUAL_IMPORT()
        algorithm
          node := Lookup.lookupClassName(Absyn.FULLYQUALIFIED(i.path), top_scope, info);
          scope := addClassToScope(Absyn.pathLastIdent(i.path), ClassTree.Entry.CLASS(node), info, scope);
        then
          ();

      else
        algorithm
          print("NFInst.addImportsToScope: IMPLEMENT ME\n");
        then
          ();

    end match;
  end for;
end addImportsToScope;

function partialInstClass
  input output InstNode node;
protected
  Instance i;
algorithm
  () := match InstNode.instance(node)
    case Instance.NOT_INSTANTIATED()
      algorithm
        i := partialInstClass2(InstNode.definition(node), node);
        node := InstNode.setInstance(i, node);
      then
        ();

    else ();
  end match;
end partialInstClass;

function partialInstClass2
  input SCode.Element definition;
  input InstNode scope;
  output Instance instance;
algorithm
  instance := match definition
    local
      SCode.ClassDef cdef;
      ClassTree.Tree classes;
      list<SCode.Element> elements;

    case SCode.CLASS(classDef = cdef as SCode.PARTS())
      algorithm
        (classes, elements) := makeScope(cdef.elementLst, scope);
      then
        Instance.PARTIAL_CLASS(classes, elements);

    else Instance.PARTIAL_CLASS(ClassTree.new(), {});
  end match;
end partialInstClass2;

function expandClass
  input output InstNode node;
algorithm
  node := match InstNode.instance(node)
    case Instance.PARTIAL_CLASS()
      then expandClass2(node);
    else node;
  end match;
end expandClass;

function expandClass2
  input output InstNode node;
protected
  SCode.Element def = InstNode.definition(node);
algorithm
  node := match def
    local
      Absyn.TypeSpec ty;
      SCode.Mod der_mod;
      SCode.Element ext;
      Instance i;
      SCode.ClassDef cdef;
      ClassTree.Tree scope;
      list<SCode.Element> elements;
      list<ComponentNode> components;
      Integer idx;
      list<Equation> eq, ieq;
      list<list<Statement>> alg, ialg;

    case SCode.CLASS(classDef = SCode.DERIVED(typeSpec = ty, modifications = der_mod))
      algorithm
        ext := SCode.EXTENDS(Absyn.typeSpecPath(ty), SCode.PUBLIC(),
          der_mod, NONE(), Absyn.dummyInfo);
        def.classDef := SCode.PARTS({ext}, {}, {}, {}, {}, {}, {}, NONE());
        i := Instance.PARTIAL_CLASS(ClassTree.new(), {ext});
        node := InstNode.setInstance(i, node);
        node := InstNode.setDefinition(def, node);
      then
        expandClass2(node);

    case SCode.CLASS(classDef = cdef as SCode.PARTS())
      algorithm
        Instance.PARTIAL_CLASS(classes = scope, elements = elements) :=
          InstNode.instance(node);

        // Change the instance to an expanded instance, to avoid instantiation loops.
        i := Instance.initExpandedClass(scope);
        node := InstNode.setInstance(i, node);

        // Expand all the extends clauses.
        (components, scope) := expandExtends(elements, def.name, node, scope);

        // Add component ID:s to the scope.
        idx := 1;
        for c in components loop
          if Component.isNamedComponent(ComponentNode.component(c)) then
            // TODO: Handle components with the same name.
            scope := ClassTree.add(scope, ComponentNode.name(c),
              ClassTree.Entry.COMPONENT(idx), ClassTree.addConflictReplace);
          end if;

          idx := idx + 1;
        end for;

        eq := instEquations(cdef.normalEquationLst, node);
        ieq := instEquations(cdef.initialEquationLst, node);
        alg := instAlgorithmSections(cdef.normalAlgorithmLst, node);
        ialg := instAlgorithmSections(cdef.initialAlgorithmLst, node);

        i := Instance.EXPANDED_CLASS(scope, listArray(components), eq, ieq, alg, ialg);
      then
        InstNode.setInstance(i, node);

    else
      algorithm
        Error.addInternalError("NFInst.expandClass2 got unknown class.", Absyn.dummyInfo);
      then
        fail();

  end match;
end expandClass2;

function expandExtends
  "This function takes a list of SCode element and expands all the extends
   clauses. This means expanding the extended classes and inserting their
   contents into the scope and element list, as well as applying any modifiers
   from the extends clause to the inherited elements. The result is a list of
   components, both local and inherited, as well as a scope filled with local
   and inherited components and classes."
  input list<SCode.Element> elements;
  input String className;
  input InstNode currentScope;
        output list<ComponentNode> components = {};
  input output ClassTree.Tree scope;
protected
  InstNode ext_node;
  Instance ext_inst;
  Modifier mod;
  ModifierScope mod_scope;
algorithm
  for e in elements loop
    () := match e
      case SCode.EXTENDS()
        algorithm
          // Look up the name and expand the class.
          ext_node := Lookup.lookupBaseClassName(e.baseClassPath, currentScope, e.info);
          // TODO: Reinstantiating the class might not be needed any more.
          ext_node := InstNode.setInstance(Instance.NOT_INSTANTIATED(), ext_node);
          ext_node := InstNode.setNodeType(InstNodeType.EXTENDS(currentScope), ext_node);
          ext_node := InstNode.rename(ext_node, className);
          ext_node := expand(ext_node);

          // Initialize the modifiers from the extends clause.
          mod_scope := ModifierScope.EXTENDS_SCOPE(e.baseClassPath);
          mod := Modifier.create(e.modifications, "", mod_scope, currentScope);

          // Apply the modifier to the expanded instance of the extended class.
          ext_inst := InstNode.instance(ext_node);
          ext_inst := applyModifier(mod, ext_inst, mod_scope);
          ext_node := InstNode.setInstance(ext_inst, ext_node);

          components := ComponentNode.newExtends(ext_node, e) :: components;
          components := addInheritedComponentRefs(ext_inst, components);
          scope := addInheritedClasses(ext_inst, scope);
        then
          ();

      case SCode.COMPONENT()
        algorithm
          // A component, add it to the list of components.
          components := ComponentNode.new(e.name, e) :: components;
        then
          ();

      else
        algorithm
          Error.addInternalError("NFInst.expandExtends got unknown element!", Absyn.dummyInfo);
        then
          fail();

    end match;
  end for;
end expandExtends;

function applyModifier
  input Modifier modifier;
  input output Instance instance;
  input ModifierScope modifierScope;
algorithm
  () := match instance
    local
      list<Modifier> mods;
      ClassTree.Tree elements;
      array<ComponentNode> components;
      ClassTree.Entry entry;

    case Instance.EXPANDED_CLASS(elements = elements, components = components)
      algorithm
        mods := Modifier.toList(modifier);

        for m in mods loop
          // Skip empty modifiers.
          if Modifier.isEmpty(m) then
            continue;
          end if;

          // Fetch the class tree entry for the element with the same name as the modifier.
          try
            entry := ClassTree.get(elements, Modifier.name(m));
          else
            Error.addSourceMessageAndFail(Error.MISSING_MODIFIED_ELEMENT,
              {Modifier.name(m), ModifierScope.name(modifierScope)}, Modifier.info(m));
          end try;

          () := match entry
            // Modifier is for a component, add it to the component in the array.
            case ClassTree.Entry.COMPONENT()
              algorithm
                components[entry.index] :=
                  ComponentNode.apply(components[entry.index], Component.setModifier, m);
              then
                ();

            case ClassTree.Entry.CLASS()
              algorithm
                print("IMPLEMENT ME: Class modifier.\n");
              then
                ();

          end match;
        end for;
      then
        ();

    case Instance.PARTIAL_BUILTIN()
      algorithm
        instance.modifier := Modifier.merge(modifier, instance.modifier);
      then
        ();


  end match;
end applyModifier;

function addInheritedComponentRefs
  input Instance extendsInstance;
  input output list<ComponentNode> components;
protected
  Integer node_idx = listLength(components);
  Integer idx = 0;
  Component comp;
algorithm
  () := match extendsInstance
    case Instance.EXPANDED_CLASS()
      algorithm
        for c in extendsInstance.components loop
          comp := ComponentNode.component(c);
          idx := idx + 1;

          components := match comp
            case Component.COMPONENT_REF() then components;
            case Component.EXTENDS_NODE()
              then addInheritedComponentRefs(
                InstNode.instance(Component.classInstance(comp)), components);
            else ComponentNode.newReference(c, node_idx, idx) :: components;
          end match;
        end for;
      then
        ();
  end match;
end addInheritedComponentRefs;

function addInheritedClasses
  input Instance extendsInstance;
  input output ClassTree.Tree scope;
algorithm
  () := match extendsInstance
    case Instance.EXPANDED_CLASS()
      algorithm
        scope := ClassTree.fold(extendsInstance.elements, addInheritedClasses2, scope);
      then
        ();
  end match;
end addInheritedClasses;

function addInheritedClasses2
  input String name;
  input ClassTree.Entry id;
  input ClassTree.Tree inScope;
  output ClassTree.Tree scope;
algorithm
  scope := match id
    case ClassTree.Entry.CLASS() then ClassTree.add(inScope, name, id);
    else inScope;
  end match;
end addInheritedClasses2;

function instClass
  input output InstNode node;
  input Modifier modifier;
protected
  Instance i = InstNode.instance(node), i_mod;
  array<ComponentNode> components;
  ClassTree.Tree scope;
  Modifier type_mod;
  list<Modifier> type_mods, inst_type_mods;
  Binding binding;
  InstNode cur_scope;
algorithm
  () := match i
    // A normal class.
    case Instance.EXPANDED_CLASS(elements = scope)
      algorithm
        // Clone the instance node, since each component needs a unique instance.
        node := InstNode.clone(node);

        // Apply the modifier to the instance.
        i_mod := applyModifier(modifier, i,
          ModifierScope.CLASS_SCOPE(InstNode.name(node)));

        // Instantiate all the components.
        components := Array.map1(Instance.components(i_mod), instComponent, node);

        // Update the instance node with the new instance.
        i_mod := Instance.INSTANCED_CLASS(scope, components,
          i.equations, i.initialEquations, i.algorithms, i.initialAlgorithms);
        node := InstNode.setInstance(i_mod, node);
      then
        ();

    // A builtin type.
    case Instance.PARTIAL_BUILTIN()
      algorithm
        node := InstNode.clone(node);
        inst_type_mods := {};
        // Merge any outer modifiers on the class with the class' own modifier.
        type_mod := Modifier.merge(modifier, i.modifier);

        // If the modifier isn't empty, instantiate it.
        if not Modifier.isEmpty(type_mod) then
          type_mods := Modifier.toList(type_mod);
          cur_scope := InstNode.parentScope(node);

          // Instantiate the binding of each submodifier.
          for m in type_mods loop
            () := match m
              case Modifier.MODIFIER()
                algorithm
                  binding := instBinding(m.binding, cur_scope);
                  m.binding := binding;
                then
                  ();

              else ();
            end match;

            inst_type_mods := m :: inst_type_mods;
          end for;
        end if;

        i_mod := Instance.INSTANCED_BUILTIN(inst_type_mods);
        node := InstNode.setInstance(i_mod, node);
      then
        ();

    else ();
  end match;
end instClass;

function instComponent
  input output ComponentNode node;
  input InstNode scope;
protected
  Component component, inst_comp;
  String name;
  SCode.Element comp;
  InstNode cls;
  Modifier comp_mod;
  Binding binding;
  DAE.Type ty;
  Component.Attributes attr;
  list<Dimension> dims;
algorithm
  component := ComponentNode.component(node);
  name := ComponentNode.name(node);

  () := match component
    case Component.COMPONENT_DEF(modifier = comp_mod as Modifier.REDECLARE())
      algorithm
        component := Component.COMPONENT_DEF(comp_mod.element, Modifier.NOMOD());
        node := ComponentNode.setComponent(component, node);
        node := instComponent(node, comp_mod.scope);
      then
        ();

    case Component.COMPONENT_DEF(definition = comp as SCode.COMPONENT())
      algorithm
        // Merge the modifier from the component.
        comp_mod := Modifier.create(comp.modifications, name,
          ModifierScope.COMPONENT_SCOPE(name), scope);
        comp_mod := Modifier.merge(component.modifier, comp_mod);
        comp_mod := Modifier.propagate(comp_mod, listLength(comp.attributes.arrayDims));

        // Instantiate the type of the component.
        cls := instTypeSpec(comp.typeSpec, comp_mod, scope, comp.info);

        // Instantiate the component's dimensions.
        dims := instDimensions(comp.attributes.arrayDims, scope);
        Modifier.checkEach(comp_mod, listEmpty(dims), name);

        // Instantiate attributes and binding.
        attr := instComponentAttributes(comp.attributes, comp.prefixes);
        binding := instBinding(Modifier.binding(comp_mod), scope);
        inst_comp := Component.UNTYPED_COMPONENT(cls, listArray(dims), binding, attr, comp.info);
        node := ComponentNode.setComponent(inst_comp, node);
      then
        ();

    case Component.EXTENDS_NODE()
      algorithm
        cls := instClass(component.node, Modifier.NOMOD());
        component.node := cls;
        node := ComponentNode.setComponent(component, node);
      then
        ();

    else ();
  end match;
end instComponent;

function instComponentAttributes
  input SCode.Attributes compAttr;
  input SCode.Prefixes compPrefs;
  output Component.Attributes attributes;
protected
  DAE.VarKind variability;
  DAE.VarDirection direction;
  DAE.VarVisibility visiblity;
  DAE.ConnectorType connectorType;
algorithm
  variability := InstUtil.translateVariability(compAttr.variability);
  direction := InstUtil.translateDirection(compAttr.direction);
  visiblity := InstUtil.translateVisibility(compPrefs.visibility);
  connectorType := InstUtil.translateConnectorType(compAttr.connectorType);
  attributes := Component.Attributes.ATTRIBUTES(variability, direction, visiblity, connectorType);
end instComponentAttributes;

function instTypeSpec
  input Absyn.TypeSpec typeSpec;
  input Modifier modifier;
  input InstNode scope;
  input SourceInfo info;
  output InstNode node;
algorithm
  node := match typeSpec
    case Absyn.TPATH()
      algorithm
        node := Lookup.lookupClassName(typeSpec.path, scope, info);
        node := instantiate(node, modifier);
      then
        node;

    case Absyn.TCOMPLEX()
      algorithm
        print("NFInst.instTypeSpec: TCOMPLEX not implemented.\n");
      then
        fail();

  end match;
end instTypeSpec;

function instModifier
  input output Modifier modifier;
algorithm

end instModifier;

function instDimension
  input Absyn.Subscript subscript;
  input InstNode scope;
  output Dimension dimension;
algorithm
  dimension := match subscript
    local
      Absyn.Exp exp;
      DAE.Exp dim_exp;
      DAE.Dimension dim;

    case Absyn.NOSUB() then Dimension.TYPED_DIM(DAE.Dimension.DIM_UNKNOWN());
    case Absyn.SUBSCRIPT(subscript = exp)
      algorithm
        exp := instExp(exp, scope);
      then
        Dimension.UNTYPED_DIM(exp, false);
    //case Absyn.SUBSCRIPT(subscript = exp)
    //  algorithm
    //    dim := match exp
    //      // Convert integer and boolean literals directly to the appropriate dimension.
    //      case Absyn.Exp.INTEGER() then DAE.Dimension.DIM_INTEGER(exp.value);
    //      else
    //        algorithm // Any other expression needs to be instantiated.
    //          (dim_exp, tree) := Inst.instExp(exp, tree);
    //        then
    //          DAE.Dimension.DIM_EXP(dim_exp);
    //    end match;
    //  then
    //    new(dim);
  end match;
end instDimension;

function instDimensions
  input Absyn.ArrayDim absynDims;
  input InstNode scope;
  output list<Dimension> dims;
algorithm
  dims := list(instDimension(dim, scope) for dim in absynDims);
end instDimensions;

//function instBindings
//  input output InstNode node;
//algorithm
//  () := match node
//    local
//      Integer idx;
//      array<Component> components;
//
//    case InstNode.INST_NODE(instance = Instance.INSTANCED_CLASS(components = components))
//      algorithm
//        idx := 1;
//        for comp in components loop
//          arrayUpdate(components, idx, instComponentBinding(comp, tree));
//          idx := +idx + 1;
//        end for;
//      then
//        ();
//
//    else ();
//  end match;
//end instBindings;

//function instComponentBinding
//  input output Component component;
//algorithm
//  () := match component
//    local
//      InstNode cls;
//      Binding binding;
//
//    case Component.UNTYPED_COMPONENT(classInst = cls)
//      algorithm
//        (cls, tree) := instBindings(component.classInst, tree);
//        component.classInst := cls;
//        (binding, tree) := instBinding(component.binding, tree);
//        component.binding := binding;
//      then
//        ();
//
//    case Component.EXTENDS_NODE()
//      algorithm
//        (cls, tree) := instBindings(component.node, tree);
//        component.node := cls;
//      then
//        ();
//
//    else ();
//  end match;
//end instComponentBinding;
//
function instBinding
  input output Binding binding;
  input InstNode scope;
algorithm
  binding := match binding
    local
      Absyn.Exp bind_exp;

    case Binding.RAW_BINDING()
      algorithm
        bind_exp := instExp(binding.bindingExp, scope);
      then
        Binding.UNTYPED_BINDING(bind_exp, false, binding.scope, binding.propagatedDims, binding.info);

    else binding;
  end match;
end instBinding;

function instExpOpt
  input output Option<Absyn.Exp> optExp;
  input InstNode scope;
algorithm
  optExp := match optExp
    local
      Absyn.Exp exp;

    case NONE() then NONE();
    case SOME(exp)
      algorithm
        exp := instExp(exp, scope);
      then
        SOME(exp);

  end match;
end instExpOpt;

function instExp
  input output Absyn.Exp absynExp;
  input InstNode scope;
algorithm
  //daeExp := match absynExp
  //  local
  //    DAE.Exp exp1, exp2;
  //    DAE.Operator op;
  //    list<DAE.Exp> expl;

  //  case Absyn.INTEGER() then DAE.ICONST(absynExp.value);
  //  case Absyn.REAL() then DAE.RCONST(stringReal(absynExp.value));
  //  case Absyn.STRING() then DAE.SCONST(absynExp.value);
  //  case Absyn.BOOL() then DAE.BCONST(absynExp.value);
  //  case Absyn.CREF()
  //    algorithm
  //      (daeExp, tree) := instCref(absynExp.componentRef, tree);
  //    then
  //      daeExp;

  //  case Absyn.BINARY()
  //    algorithm
  //      (exp1, tree) := instExp(absynExp.exp1, tree);
  //      (exp2, tree) := instExp(absynExp.exp2, tree);
  //      op := instOperator(absynExp.op);
  //    then
  //      DAE.BINARY(exp1, op, exp2);

  //  case Absyn.UNARY()
  //    algorithm
  //      (exp1, tree) := instExp(absynExp.exp, tree);
  //      op := instOperator(absynExp.op);
  //    then
  //      DAE.UNARY(op, exp1);

  //  case Absyn.LBINARY()
  //    algorithm
  //      (exp1, tree) := instExp(absynExp.exp1, tree);
  //      (exp2, tree) := instExp(absynExp.exp2, tree);
  //      op := instOperator(absynExp.op);
  //    then
  //      DAE.LBINARY(exp1, op, exp2);

  //  case Absyn.LUNARY()
  //    algorithm
  //      (exp1, tree) := instExp(absynExp.exp, tree);
  //      op := instOperator(absynExp.op);
  //    then
  //      DAE.LUNARY(op, exp1);

  //  case Absyn.RELATION()
  //    algorithm
  //      (exp1, tree) := instExp(absynExp.exp1, tree);
  //      (exp2, tree) := instExp(absynExp.exp2, tree);
  //      op := instOperator(absynExp.op);
  //    then
  //      DAE.RELATION(exp1, op, exp2, 0, NONE());

  //  case Absyn.ARRAY()
  //    algorithm
  //      (expl, tree) := List.mapFold(absynExp.arrayExp, instExp, tree);
  //    then
  //      DAE.ARRAY(DAE.T_UNKNOWN_DEFAULT, false, expl);

  //  case Absyn.MATRIX()
  //    algorithm
  //      (expl, tree) := List.mapFold(list(Absyn.ARRAY(e) for e in absynExp.matrix), instExp, tree);
  //    then
  //      DAE.ARRAY(DAE.T_UNKNOWN_DEFAULT, false, expl);

  //  else DAE.SCONST("ERROR");
  //end match;
end instExp;

function instCref
  input output Absyn.ComponentRef cref;
  input InstNode scope;
algorithm

  //daeCref := match absynCref
  //  local
  //    DAE.ComponentRef cref;

  //  case Absyn.CREF_IDENT()
  //    then DAE.CREF_IDENT(absynCref.name, DAE.T_UNKNOWN_DEFAULT, {});

  //  case Absyn.CREF_QUAL()
  //    algorithm
  //      (cref, tree) := instCref(absynCref.componentRef, tree);
  //    then
  //      DAE.CREF_QUAL(absynCref.name, DAE.T_UNKNOWN_DEFAULT, {}, cref);

  //  case Absyn.CREF_FULLYQUALIFIED()
  //    algorithm
  //      (cref, tree) := instCref(absynCref.componentRef, tree);
  //    then
  //      cref;

  //  case Absyn.WILD() then DAE.WILD();
  //  case Absyn.ALLWILD() then DAE.WILD();

  //end match;
end instCref;

function instEquations
  input list<SCode.Equation> scodeEql;
  input InstNode scope;
  output list<Equation> instEql;
algorithm
  instEql := list(instEquation(eq, scope) for eq in scodeEql);
end instEquations;

function instEquation
  input SCode.Equation scodeEq;
  input InstNode scope;
  output Equation instEq;
protected
  SCode.EEquation eq;
algorithm
  SCode.EQUATION(eEquation = eq) := scodeEq;
  instEq := instEEquation(eq, scope);
end instEquation;

function instEEquations
  input list<SCode.EEquation> scodeEql;
  input InstNode scope;
  output list<Equation> instEql;
algorithm
  instEql := list(instEEquation(eq, scope) for eq in scodeEql);
end instEEquations;

function instEEquation
  input SCode.EEquation scodeEq;
  input InstNode scope;
  output Equation instEq;
algorithm
  instEq := match scodeEq
    local
      Absyn.Exp exp1, exp2, exp3;
      Absyn.ComponentRef cr1, cr2;
      Option<Absyn.Exp> oexp;
      list<Equation> eql;
      list<Absyn.Exp> expl;
      list<tuple<Absyn.Exp, list<Equation>>> branches;

    case SCode.EQ_EQUALS()
      algorithm
        exp1 := instExp(scodeEq.expLeft, scope);
        exp2 := instExp(scodeEq.expRight, scope);
      then
        Equation.UNTYPED_EQUALITY(exp1, exp2, scodeEq.info);

    case SCode.EQ_CONNECT()
      algorithm
        cr1 := instCref(scodeEq.crefLeft, scope);
        cr2 := instCref(scodeEq.crefRight, scope);
      then
        Equation.UNTYPED_CONNECT(cr1, cr2, scodeEq.info);

    case SCode.EQ_FOR()
      algorithm
        oexp := instExpOpt(scodeEq.range, scope);
        eql := instEEquations(scodeEq.eEquationLst, scope);
      then
        Equation.UNTYPED_FOR(scodeEq.index, oexp, eql, scodeEq.info);

    case SCode.EQ_IF()
      algorithm
        // Instantiate the conditions.
        expl := list(instExp(c, scope) for c in scodeEq.condition);

        // Instantiate each branch and pair it up with a condition.
        branches := {};
        for branch in scodeEq.thenBranch loop
          eql := instEEquations(scodeEq.elseBranch, scope);
          exp1 :: expl := expl;
          branches := (exp1, eql) :: branches;
        end for;

        // Instantiate the else-branch, if there is one, and make it a branch
        // with condition true.
        if not listEmpty(scodeEq.elseBranch) then
          eql := instEEquations(scodeEq.elseBranch, scope);
          branches := (Absyn.BOOL(true), eql) :: branches;
        end if;
      then
        Equation.UNTYPED_IF(listReverse(branches), scodeEq.info);

    case SCode.EQ_WHEN()
      algorithm
        exp1 := instExp(scodeEq.condition, scope);
        eql := instEEquations(scodeEq.eEquationLst, scope);
        branches := {(exp1, eql)};

        for branch in scodeEq.elseBranches loop
          exp1 := instExp(Util.tuple21(branch), scope);
          eql := instEEquations(Util.tuple22(branch), scope);
          branches := (exp1, eql) :: branches;
        end for;
      then
        Equation.UNTYPED_WHEN(branches, scodeEq.info);

    case SCode.EQ_ASSERT()
      algorithm
        exp1 := instExp(scodeEq.condition, scope);
        exp2 := instExp(scodeEq.message, scope);
        exp3 := instExp(scodeEq.level, scope);
      then
        Equation.UNTYPED_ASSERT(exp1, exp2, exp3, scodeEq.info);

    case SCode.EQ_TERMINATE()
      algorithm
        exp1 := instExp(scodeEq.message, scope);
      then
        Equation.UNTYPED_TERMINATE(exp1, scodeEq.info);

    case SCode.EQ_REINIT()
      algorithm
        cr1 := instCref(scodeEq.cref, scope);
        exp1 := instExp(scodeEq.expReinit, scope);
      then
        Equation.UNTYPED_REINIT(cr1, exp1, scodeEq.info);

    case SCode.EQ_NORETCALL()
      algorithm
        exp1 := instExp(scodeEq.exp, scope);
      then
        Equation.UNTYPED_NORETCALL(exp1, scodeEq.info);

    else
      algorithm
        Error.addInternalError("NFInst.instEEquation: Unknown equation",
          SCode.getEEquationInfo(scodeEq));
      then
        fail();

  end match;
end instEEquation;

function instAlgorithmSections
  input list<SCode.AlgorithmSection> algorithmSections;
  input InstNode scope;
  output list<list<Statement>> statements;
algorithm
  statements := list(instAlgorithmSection(alg, scope) for alg in algorithmSections);
end instAlgorithmSections;

function instAlgorithmSection
  input SCode.AlgorithmSection algorithmSection;
  input InstNode scope;
  output list<Statement> statements;
algorithm
  statements := instStatements(algorithmSection.statements, scope);
end instAlgorithmSection;

function instStatements
  input list<SCode.Statement> scodeStmtl;
  input InstNode scope;
  output list<Statement> statements;
algorithm
  statements := list(instStatement(stmt, scope) for stmt in scodeStmtl);
end instStatements;

function instStatement
  input SCode.Statement scodeStmt;
  input InstNode scope;
  output Statement statement;
algorithm
  statement := match scodeStmt
    local
      Absyn.Exp exp1, exp2, exp3;
      Absyn.ComponentRef cr;
      Option<Absyn.Exp> oexp;
      list<Statement> stmtl;
      list<tuple<Absyn.Exp, list<Statement>>> branches;

    case SCode.ALG_ASSIGN()
      algorithm
        exp1 := instExp(scodeStmt.assignComponent, scope);
        exp2 := instExp(scodeStmt.value, scope);
      then
        Statement.UNTYPED_ASSIGNMENT(exp1, exp2, scodeStmt.info);

    case SCode.ALG_FOR()
      algorithm
        oexp := instExpOpt(scodeStmt.range, scope);
        stmtl := instStatements(scodeStmt.forBody, scope);
      then
        Statement.UNTYPED_FOR(scodeStmt.index, oexp, stmtl, scodeStmt.info);

    case SCode.ALG_IF()
      algorithm
        branches := {};
        for branch in (scodeStmt.boolExpr, scodeStmt.trueBranch) :: scodeStmt.elseIfBranch loop
          exp1 := instExp(Util.tuple21(branch), scope);
          stmtl := instStatements(Util.tuple22(branch), scope);
          branches := (exp1, stmtl) :: branches;
        end for;

        stmtl := instStatements(scodeStmt.elseBranch, scope);
        branches := listReverse((Absyn.BOOL(true), stmtl) :: branches);
      then
        Statement.UNTYPED_IF(branches, scodeStmt.info);

    case SCode.ALG_WHEN_A()
      algorithm
        branches := {};
        for branch in scodeStmt.branches loop
          exp1 := instExp(Util.tuple21(branch), scope);
          stmtl := instStatements(Util.tuple22(branch), scope);
          branches := (exp1, stmtl) :: branches;
        end for;
      then
        Statement.UNTYPED_WHEN(listReverse(branches), scodeStmt.info);

    case SCode.ALG_ASSERT()
      algorithm
        exp1 := instExp(scodeStmt.condition, scope);
        exp2 := instExp(scodeStmt.message, scope);
        exp3 := instExp(scodeStmt.level, scope);
      then
        Statement.UNTYPED_ASSERT(exp1, exp2, exp3, scodeStmt.info);

    case SCode.ALG_TERMINATE()
      algorithm
        exp1 := instExp(scodeStmt.message, scope);
      then
        Statement.UNTYPED_TERMINATE(exp1, scodeStmt.info);

    case SCode.ALG_REINIT()
      algorithm
        cr := instCref(scodeStmt.cref, scope);
        exp1 := instExp(scodeStmt.newValue, scope);
      then
        Statement.UNTYPED_REINIT(cr, exp1, scodeStmt.info);

    case SCode.ALG_NORETCALL()
      algorithm
        exp1 := instExp(scodeStmt.exp, scope);
      then
        Statement.UNTYPED_NORETCALL(exp1, scodeStmt.info);

    case SCode.ALG_WHILE()
      algorithm
        exp1 := instExp(scodeStmt.boolExpr, scope);
        stmtl := instStatements(scodeStmt.whileBody, scope);
      then
        Statement.UNTYPED_WHILE(exp1, stmtl, scodeStmt.info);

    case SCode.ALG_RETURN() then Statement.RETURN(scodeStmt.info);
    case SCode.ALG_BREAK() then Statement.BREAK(scodeStmt.info);

    case SCode.ALG_FAILURE()
      algorithm
        stmtl := instStatements(scodeStmt.stmts, scope);
      then
        Statement.FAILURE(stmtl, scodeStmt.info);

    else
      algorithm
        Error.addInternalError("NFInst.instStatement: Unknown statement",
          SCode.getStatementInfo(scodeStmt));
      then
        fail();

  end match;
end instStatement;

annotation(__OpenModelica_Interface="frontend");
end NFInst;
