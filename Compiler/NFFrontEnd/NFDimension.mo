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

encapsulated uniontype NFDimension
protected
  import Dimension = NFDimension;
  import Operator = NFOperator;
  import Prefixes = NFPrefixes;

public
  import Absyn.{Exp, Path, Subscript};
  import Dump;
  import NFClass.Class;
  import Expression = NFExpression;
  import NFInstNode.InstNode;
  import Type = NFType;
  import ComponentRef = NFComponentRef;
  import NFPrefixes.Variability;
  import Inst = NFInst;

  record RAW_DIM
    Absyn.Subscript dim;
    InstNode scope;
  end RAW_DIM;

  record UNTYPED
    Expression dimension;
    Boolean isProcessing;
  end UNTYPED;

  record INTEGER
    Integer size;
    Variability var;
  end INTEGER;

  record BOOLEAN
  end BOOLEAN;

  record ENUM
    Type enumType;
  end ENUM;

  record EXP
    Expression exp;
    Variability var;
  end EXP;

  record UNKNOWN
  end UNKNOWN;

  function fromExp
    input Expression exp;
    input Variability var;
    output Dimension dim;
  algorithm
    dim := match exp
      local
        Class cls;
        ComponentRef cref;
        Type ty;

      case Expression.INTEGER() then INTEGER(exp.value, var);

      case Expression.TYPENAME(ty = Type.ARRAY(elementType = ty))
        then
          match ty
            case Type.BOOLEAN() then BOOLEAN();
            case Type.ENUMERATION() then ENUM(ty);
            else
              algorithm
                Error.assertion(false, getInstanceName() + " got invalid typename", sourceInfo());
              then
                fail();
          end match;

      else Dimension.EXP(exp, var);
    end match;
  end fromExp;

  function fromInteger
    input Integer n;
    output Dimension dim = INTEGER(n, Variability.CONSTANT);
  end fromInteger;

  function fromExpList
    input list<Expression> expl;
    output Dimension dim = INTEGER(listLength(expl), Variability.CONSTANT);
  end fromExpList;

  function toDAE
    input Dimension dim;
    output DAE.Dimension daeDim;
  algorithm
    daeDim := match dim
      local
        Type ty;

      case INTEGER() then DAE.DIM_INTEGER(dim.size);
      case BOOLEAN() then DAE.DIM_BOOLEAN();
      case ENUM(enumType = ty as Type.ENUMERATION())
        then DAE.DIM_ENUM(ty.typePath, ty.literals, listLength(ty.literals));
      case EXP() then DAE.DIM_EXP(Expression.toDAE(dim.exp));
      case UNKNOWN() then DAE.DIM_UNKNOWN();
    end match;
  end toDAE;

  function add
    input Dimension a, b;
    output Dimension c;
  algorithm
    c := match (a, b)
      case (UNKNOWN(),_) then UNKNOWN();
      case (_,UNKNOWN()) then UNKNOWN();
      case (INTEGER(),INTEGER()) then INTEGER(a.size+b.size, Prefixes.variabilityMax(a.var, b.var));
      case (INTEGER(),EXP()) then EXP(Expression.BINARY(b.exp, Operator.OPERATOR(Type.INTEGER(), NFOperator.Op.ADD), Expression.INTEGER(a.size)), b.var);
      case (EXP(),INTEGER()) then EXP(Expression.BINARY(a.exp, Operator.OPERATOR(Type.INTEGER(), NFOperator.Op.ADD), Expression.INTEGER(b.size)), a.var);
      case (EXP(),EXP()) then EXP(Expression.BINARY(a.exp, Operator.OPERATOR(Type.INTEGER(), NFOperator.Op.ADD), b.exp), Prefixes.variabilityMax(a.var, b.var));
      else UNKNOWN();
    end match;
  end add;

  function size
    input Dimension dim;
    output Integer size;
  algorithm
    size := match dim
      local
        Type ty;

      case INTEGER() then dim.size;
      case BOOLEAN() then 2;
      case ENUM(enumType = ty as Type.ENUMERATION()) then listLength(ty.literals);
    end match;
  end size;

  function isEqual
    input Dimension dim1;
    input Dimension dim2;
    output Boolean isEqual;
  algorithm
    isEqual := match (dim1, dim2)
      case (UNKNOWN(), _) then true;
      case (_, UNKNOWN()) then true;
      case (EXP(), _) then true;
      case (_, EXP()) then true;
      else Dimension.size(dim1) == Dimension.size(dim2);
    end match;
  end isEqual;

  function isEqualKnown
    input Dimension dim1;
    input Dimension dim2;
    output Boolean isEqual;
  algorithm
    isEqual := match (dim1, dim2)
      case (UNKNOWN(), _) then false;
      case (_, UNKNOWN()) then false;
      case (EXP(), EXP()) then Expression.isEqual(dim1.exp, dim2.exp);
      case (EXP(), _) then false;
      case (_, EXP()) then false;
      else Dimension.size(dim1) == Dimension.size(dim2);
    end match;
  end isEqualKnown;

  public function allEqualKnown
    input list<Dimension> dims1;
    input list<Dimension> dims2;
    output Boolean allEqual;
  algorithm
    allEqual := match(dims1, dims2)
      local
        Dimension dim1, dim2;
        list<Dimension> rest1, rest2;

      case ({}, {}) then true;
      case (dim1::rest1, dim2::rest2) guard isEqualKnown(dim1, dim2)
        then allEqualKnown(rest1, rest2);
      else false;
    end match;
  end allEqualKnown;

  function isKnown
    input Dimension dim;
    output Boolean known;
  algorithm
    known := match dim
      case INTEGER() then true;
      case BOOLEAN() then true;
      case ENUM() then true;
      else false;
    end match;
  end isKnown;

  function subscriptType
    "Returns the expected type of a subscript for the given dimension."
    input Dimension dim;
    output Type ty;
  algorithm
    ty := match dim
      case INTEGER() then Type.INTEGER();
      case BOOLEAN() then Type.BOOLEAN();
      case ENUM() then dim.enumType;
      case EXP() then Expression.typeOf(dim.exp);
      else Type.UNKNOWN();
    end match;
  end subscriptType;

  function toString
    input Dimension dim;
    output String str;
  algorithm
    str := match dim
      local
        Type ty;

      case INTEGER() then String(dim.size);
      case BOOLEAN() then "Boolean";
      case ENUM(enumType = ty as Type.ENUMERATION()) then Absyn.pathString(ty.typePath);
      case EXP() then Expression.toString(dim.exp);
      case UNKNOWN() then ":";
      case UNTYPED() then Expression.toString(dim.dimension);
    end match;
  end toString;

  function toStringList
    input list<Dimension> dims;
    output String str = "[" + stringDelimitList(List.map(dims, toString), ", ") + "]";
  algorithm
  end toStringList;

  function sizeExp
    "Returns the size of a dimension as an expression."
    input Dimension dim;
    input ComponentRef cref;
    input Integer index;
    output Expression sizeExp;
  algorithm
    sizeExp := match dim
      local
        Type ty;

      case INTEGER() then Expression.INTEGER(dim.size);
      case BOOLEAN() then Expression.BOOLEAN(true);
      case ENUM(enumType = ty as Type.ENUMERATION())
        then Expression.makeEnumLiteral(ty, listLength(ty.literals));
      case EXP() then dim.exp;
      case UNKNOWN()
        then Expression.SIZE(Expression.CREF(Type.INTEGER(), ComponentRef.stripSubscripts(cref)),
                             SOME(Expression.INTEGER(index)));
    end match;
  end sizeExp;

  function setScope
    input Dimension dim;
    input InstNode scope;
    output Dimension outDim;
  algorithm
    outDim := match dim
      case RAW_DIM() then RAW_DIM(dim.dim, scope);
      else dim;
    end match;
  end setScope;

  function variability
    input Dimension dim;
    output Variability var;
  algorithm
    var := match dim
      case INTEGER() then dim.var;
      case BOOLEAN() then Variability.CONSTANT;
      case ENUM() then Variability.CONSTANT;
      case EXP() then dim.var;
      case UNKNOWN() then Variability.CONTINUOUS;
    end match;
  end variability;

annotation(__OpenModelica_Interface="frontend");
end NFDimension;
