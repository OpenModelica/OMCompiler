/*
 * This file is part of OpenModelica.
 *
 * Copyright (c) 1998-CurrentYear, Linköping University,
 * Department of Computer and Information Science,
 * SE-58183 Linköping, Sweden.
 *
 * All rights reserved.
 *
 * THIS PROGRAM IS PROVIDED UNDER THE TERMS OF GPL VERSION 3
 * AND THIS OSMC PUBLIC LICENSE (OSMC-PL).
 * ANY USE, REPRODUCTION OR DISTRIBUTION OF THIS PROGRAM CONSTITUTES RECIPIENT'S
 * ACCEPTANCE OF THE OSMC PUBLIC LICENSE.
 *
 * The OpenModelica software and the Open Source Modelica
 * Consortium (OSMC) Public License (OSMC-PL) are obtained
 * from Linköping University, either from the above address,
 * from the URLs: http://www.ida.liu.se/projects/OpenModelica or
 * http://www.openmodelica.org, and in the OpenModelica distribution.
 * GNU version 3 is obtained from: http://www.gnu.org/copyleft/gpl.html.
 *
 * This program is distributed WITHOUT ANY WARRANTY; without
 * even the implied warranty of  MERCHANTABILITY or FITNESS
 * FOR A PARTICULAR PURPOSE, EXCEPT AS EXPRESSLY SET FORTH
 * IN THE BY RECIPIENT SELECTED SUBSIDIARY LICENSE CONDITIONS
 * OF OSMC-PL.
 *
 * See the full OSMC Public License conditions for more details.
 *
 */

encapsulated package NFFlatten
" file:        NFFlatten.mo
  package:     NFFlatten
  description: Flattening


  New instantiation, enable with +d=newInst.
"

import Inst = NFInst;
import NFBinding.Binding;
import NFClass.Class;
import NFComponent.Component;
import NFEquation.Equation;
import NFInstNode.InstNode;
import NFPrefix.Prefix;
import NFStatement.Statement;

import DAE;
import Error;
import Expression;
import ExpressionDump;
import ExpressionSimplify;
import List;
import SCode;
import System;
import Util;

protected
import DAEUtil;

public
partial function ExpandScalarFunc<ElementT>
  input ElementT element;
  input Prefix prefix;
  input output list<DAE.Element> elements;
end ExpandScalarFunc;

function flatten
  input InstNode classInst;
  output DAE.DAElist dae;
protected
  list<DAE.Element> elems;
  DAE.Element class_elem;
algorithm
  elems := flattenNode(classInst);
  elems := listReverse(elems);
  class_elem := DAE.COMP(InstNode.name(classInst), elems, DAE.emptyElementSource, NONE());
  dae := DAE.DAE({class_elem});
end flatten;

function flattenNode
  input InstNode node;
  input Prefix prefix = Prefix.NO_PREFIX();
  input list<DAE.Element> inElements = {};
  output list<DAE.Element> elements;
algorithm
  elements := flattenClass(InstNode.getClass(node), prefix, inElements);
end flattenNode;

function flattenClass
  input Class instance;
  input Prefix prefix;
  input output list<DAE.Element> elements;
algorithm
  _ := match instance
    case Class.INSTANCED_CLASS()
      algorithm
        for c in instance.components loop
          elements := flattenComponent(c, prefix, elements);
        end for;

        elements := flattenEquations(instance.equations, elements);
        elements := flattenInitialEquations(instance.initialEquations, elements);
        elements := flattenAlgorithms(instance.algorithms, elements);
        elements := flattenInitialAlgorithms(instance.initialAlgorithms, elements);
      then
        ();

    else
      algorithm
        print("Got non-instantiated component " + Prefix.toString(prefix) + "\n");
      then
        ();

  end match;
end flattenClass;

function flattenComponent
  input InstNode component;
  input Prefix prefix;
  input output list<DAE.Element> elements;
protected
  Component c = InstNode.component(component);
  Prefix new_pre;
  DAE.Type ty;
algorithm
  _ := match c
    case Component.TYPED_COMPONENT()
      algorithm
        ty := Component.getType(c);
        new_pre := Prefix.add(InstNode.name(component), {}, ty, prefix);

        elements := match ty
          case DAE.T_ARRAY()
            then flattenArray(Component.unliftType(c), ty.dims, new_pre, flattenScalar, elements);
          else flattenScalar(c, new_pre, elements);
        end match;
      then
        ();

    else
      algorithm
        assert(false, "flattenComponent got unknown component");
      then
        fail();

  end match;
end flattenComponent;

function flattenArray<ElementT>
  input ElementT element;
  input list<DAE.Dimension> dimensions;
  input Prefix prefix;
  input ExpandScalarFunc scalarFunc;
  input output list<DAE.Element> elements;
  input list<DAE.Subscript> subscripts = {};
protected
  DAE.Dimension dim;
  list<DAE.Dimension> rest_dims;
  Prefix sub_pre;
  DAE.ComponentRef cr;
  Option<DAE.Exp> oe;
  DAE.Exp e;
  Integer i;
algorithm
  if listEmpty(dimensions) then
    sub_pre := Prefix.setSubscripts(listReverse(subscripts), prefix);
    elements := scalarFunc(element, sub_pre, elements);
  else
    dim :: rest_dims := dimensions;
    elements := matchcontinue dim
      case DAE.DIM_INTEGER()
        then flattenArrayIntDim(element, dim.integer, rest_dims, prefix,
            subscripts, scalarFunc, elements);
      case DAE.DIM_ENUM()
        then flattenArrayEnumDim(element, dim.enumTypeName, dim.literals,
            rest_dims, prefix, subscripts, scalarFunc, elements);
      case DAE.DIM_EXP(DAE.CREF(componentRef = cr))
        algorithm
          SOME(DAE.ICONST(i)) := DAEUtil.evaluateCref(cr, elements);
        then flattenArrayIntDim(element, i, rest_dims, prefix,
                                           subscripts, scalarFunc, elements);
      else
        algorithm
          print("Unknown dimension " + ExpressionDump.dimensionString(dim) +
            " in NFFlatten.flattenArray\n");
        then
          fail();
    end matchcontinue;
  end if;
end flattenArray;

function flattenArrayIntDim<ElementT>
  input ElementT element;
  input Integer dimSize;
  input list<DAE.Dimension> restDims;
  input Prefix prefix;
  input list<DAE.Subscript> subscripts;
  input ExpandScalarFunc scalarFunc;
  input output list<DAE.Element> elements;
protected
  list<DAE.Subscript> subs;
algorithm
  for i in 1:dimSize loop
    subs := DAE.INDEX(DAE.ICONST(i)) :: subscripts;
    elements := flattenArray(element, restDims, prefix, scalarFunc, elements, subs);
  end for;
end flattenArrayIntDim;

function flattenArrayEnumDim<ElementT>
  input ElementT element;
  input Absyn.Path typeName;
  input list<String> literals;
  input list<DAE.Dimension> restDims;
  input Prefix prefix;
  input list<DAE.Subscript> subscripts;
  input ExpandScalarFunc scalarFunc;
  input output list<DAE.Element> elements;
protected
  Integer i = 1;
  DAE.Exp enum_exp;
  list<DAE.Subscript> subs;
algorithm
  for l in literals loop
    enum_exp := DAE.ENUM_LITERAL(Absyn.suffixPath(typeName, l), i);
    i := i + 1;

    subs := DAE.INDEX(enum_exp) :: subscripts;
    elements := flattenArray(element, restDims, prefix, scalarFunc, elements, subs);
  end for;
end flattenArrayEnumDim;

function flattenScalar
  input Component component;
  input Prefix prefix;
  input output list<DAE.Element> elements;
algorithm
  _ := match component
    local
      Class i;
      DAE.Element var;
      DAE.ComponentRef cref;
      Component.Attributes attr;
      list<DAE.Dimension> dims;
      Option<DAE.Exp> binding_exp;

    case Component.TYPED_COMPONENT()
      algorithm
        i := InstNode.getClass(component.classInst);

        elements := match i
          case Class.INSTANCED_BUILTIN()
            algorithm
              cref := Prefix.toCref(prefix);
              binding_exp := flattenBinding(component.binding, prefix);
              attr := component.attributes;

              var := DAE.VAR(
                cref,
                attr.variability,
                attr.direction,
                DAE.NON_PARALLEL(),
                attr.visibility,
                component.ty,
                binding_exp,
                {},
                attr.connectorType,
                DAE.emptyElementSource,
                NONE(),
                NONE(),
                Absyn.NOT_INNER_OUTER());
            then
              var :: elements;

          else flattenClass(i, prefix, elements);
        end match;
      then
        ();

    else
      algorithm
        assert(false, getInstanceName() + " got untyped component.");
      then
        fail();

  end match;
end flattenScalar;

function flattenBinding
  input Binding binding;
  input Prefix prefix;
  output Option<DAE.Exp> bindingExp;
algorithm
  bindingExp := match binding
    local
      list<DAE.Subscript> subs;

    case Binding.UNBOUND() then NONE();

    case Binding.TYPED_BINDING(propagatedDims = -1)
      then SOME(binding.bindingExp);

    case Binding.TYPED_BINDING()
      algorithm
        // TODO: Implement this in a saner way.
        subs := List.lastN(List.flatten(Prefix.allSubscripts(prefix)),
          binding.propagatedDims);
      then
        SOME(Expression.subscriptExp(binding.bindingExp, subs));

    else
      algorithm
        assert(false, getInstanceName() + " got untyped binding.");
      then
        fail();

  end match;
end flattenBinding;

function flattenEquation
  input Equation eq;
  input output list<DAE.Element> elements = {};
protected
  list<DAE.Element> els = {}, els1, els2;
  DAE.Exp e;
  Option<DAE.Exp> oe;
  list<DAE.Exp> range;
algorithm
  elements := match eq
    local
      DAE.Exp lhs, rhs;
      Integer is, ie, step;

    case Equation.EQUALITY()
      then DAE.EQUATION(eq.lhs, eq.rhs, DAE.emptyElementSource) :: elements;

    case Equation.IF()
      then flattenIfEquation(eq.branches, false) :: elements;

    case Equation.FOR()
      algorithm
        // flatten the equations
        els1 := List.flatten(List.map1(eq.body, flattenEquation, {}));
        // deal with the range
        if isSome(eq.range) then
          SOME(e) := eq.range;
          SOME(e) := DAEUtil.evaluateExp(e, elements);
          range := match (e)
                    case DAE.ARRAY(array = range) then range;
                    case DAE.RANGE(_, DAE.ICONST(is), SOME(DAE.ICONST(step)), DAE.ICONST(ie))
                      then List.map(ExpressionSimplify.simplifyRange(is, step, ie), Expression.makeIntegerExp);
                    case DAE.RANGE(_, DAE.ICONST(is), _, DAE.ICONST(ie))
                      then if is <= ie
                           then List.map(ExpressionSimplify.simplifyRange(is, 1, ie), Expression.makeIntegerExp)
                           else List.map(ExpressionSimplify.simplifyRange(is, -1, ie), Expression.makeIntegerExp);
                  end match;
          // replace index in elements
          for i in range loop
            els := DAEUtil.replaceCrefInDAEElements(els1, DAE.CREF_IDENT(eq.name, eq.indexType, {}), i);
            elements := listAppend(els, elements);
          end for;
        end if;
      then
        elements;

    case Equation.WHEN()
      then
        flattenWhenEquation(eq.branches)::elements;

    else elements;
  end match;
end flattenEquation;

function flattenEquations
  input list<Equation> equations;
  input output list<DAE.Element> elements = {};
algorithm
  elements := List.fold(equations, flattenEquation, elements);
end flattenEquations;

function flattenInitialEquation
  input Equation eq;
  input output list<DAE.Element> elements;
algorithm
  elements := match eq
    local
      DAE.Exp lhs, rhs;

    case Equation.EQUALITY()
      then DAE.INITIALEQUATION(eq.lhs, eq.rhs, DAE.emptyElementSource) :: elements;

    case Equation.IF()
      then flattenIfEquation(eq.branches, true) :: elements;

    else elements;
  end match;
end flattenInitialEquation;

function flattenInitialEquations
  input list<Equation> equations;
  input output list<DAE.Element> elements = {};
algorithm
  elements := List.fold(equations, flattenInitialEquation, elements);
end flattenInitialEquations;

function flattenIfEquation
  input list<tuple<DAE.Exp, list<Equation>>> ifBranches;
  input Boolean isInitial;
  output DAE.Element ifEquation;
protected
  list<DAE.Exp> conditions = {};
  list<DAE.Element> branch, else_branch;
  list<list<DAE.Element>> branches = {};
algorithm
  for b in ifBranches loop
    conditions := Util.tuple21(b) :: conditions;
    branches := flattenEquations(Util.tuple22(b)) :: branches;
  end for;

  // Transform the last branch to an else-branch if its condition is true.
  if Expression.isConstTrue(listHead(conditions)) then
    conditions := listRest(conditions);
    else_branch := listHead(branches);
    branches := listRest(branches);
  else
    else_branch := {};
  end if;

  conditions := listReverse(conditions);
  branches := listReverse(branches);

  if isInitial then
    ifEquation := DAE.INITIAL_IF_EQUATION(conditions, branches, else_branch,
      DAE.emptyElementSource);
  else
    ifEquation := DAE.IF_EQUATION(conditions, branches, else_branch,
      DAE.emptyElementSource);
  end if;
end flattenIfEquation;

function flattenAlgorithm
  input list<Statement> algSection;
  input output list<DAE.Element> elements;
algorithm

end flattenAlgorithm;

function flattenAlgorithms
  input list<list<Statement>> algorithms;
  input output list<DAE.Element> elements = {};
algorithm
  elements := List.fold(algorithms, flattenAlgorithm, elements);
end flattenAlgorithms;

function flattenInitialAlgorithm
  input list<Statement> algSection;
  input output list<DAE.Element> elements;
algorithm

end flattenInitialAlgorithm;

function flattenInitialAlgorithms
  input list<list<Statement>> algorithms;
  input output list<DAE.Element> elements = {};
algorithm
  elements := List.fold(algorithms, flattenInitialAlgorithm, elements);
end flattenInitialAlgorithms;

function flattenWhenEquation
  input list<tuple<DAE.Exp, list<Equation>>> whenBranches;
  output DAE.Element whenEquation;
protected
  DAE.Exp cond1,cond2;
  list<DAE.Element> els1, els2;
  tuple<DAE.Exp, list<Equation>> head;
  list<tuple<DAE.Exp, list<Equation>>> rest;
  Option<DAE.Element> owhenEquation = NONE();
algorithm

  head::rest := whenBranches;
  cond1 := Util.tuple21(head);
  els1 := flattenEquations(Util.tuple22(head));
  rest := listReverse(rest);

  for b in rest loop
    cond2 := Util.tuple21(b);
    els2 := flattenEquations(Util.tuple22(b));
    whenEquation := DAE.WHEN_EQUATION(cond2, els2,  owhenEquation, DAE.emptyElementSource);
    owhenEquation := SOME(whenEquation);
  end for;

  whenEquation := DAE.WHEN_EQUATION(cond1, els1,  owhenEquation, DAE.emptyElementSource);

end flattenWhenEquation;

annotation(__OpenModelica_Interface="frontend");
end NFFlatten;
