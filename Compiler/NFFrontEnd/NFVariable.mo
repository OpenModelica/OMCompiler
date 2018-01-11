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

encapsulated uniontype NFVariable
  import Binding = NFBinding;
  import NFComponent.Component;
  import ComponentRef = NFComponentRef;
  import Expression = NFExpression;
  import NFInstNode.InstNode;
  import NFPrefixes.Visibility;
  import Type = NFType;

protected
  import Variable = NFVariable;

public
  record VARIABLE
    ComponentRef name;
    Type ty;
    Binding binding;
    Visibility visibility;
    Component.Attributes attributes;
    list<tuple<String, Binding>> typeAttributes;
    SourceInfo info;
  end VARIABLE;

  function fromCref
    input ComponentRef cref;
    output Variable variable;
  protected
    InstNode node;
    Component comp;
    Type ty;
    Binding binding;
    Visibility vis;
    Component.Attributes attr;
    SourceInfo info;
  algorithm
    node := ComponentRef.node(cref);
    comp := InstNode.component(node);
    ty := ComponentRef.getType(cref);
    binding := Component.getBinding(comp);
    vis := InstNode.visibility(node);
    attr := Component.getAttributes(comp);
    info := InstNode.info(node);
    variable := VARIABLE(cref, ty, binding, vis, attr, {}, info);
  end fromCref;

  annotation(__OpenModelica_Interface="frontend");
end NFVariable;
