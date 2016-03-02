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

encapsulated package SimpleModelicaParser

import LexerModelicaDiff.{Token,TokenId,tokenContent,printToken,modelicaDiffTokenEq};

protected

import DiffAlgorithm;
import DiffAlgorithm.{diff,Diff};
import Error;
import Print;
import StackOverflow;
import System;
import List;
import StringUtil;
import MetaModelica.Dangerous.listReverseInPlace;

public

uniontype ParseTree
  record EMPTY
  end EMPTY;
  record NODE
    ParseTree label;
    list<ParseTree> nodes;
  end NODE;
  record LEAF
    Token token;
  end LEAF;
end ParseTree;

function parseTreeStr
  input list<ParseTree> trees;
  output String str;
protected
  Integer i;
algorithm
  i := Print.saveAndClearBuf();
  try
    for tree in trees loop
      parseTreeStrWork(tree);
    end for;
    str := Print.getString();
    Print.restoreBuf(i);
  else
    Print.restoreBuf(i);
    fail();
  end try;
end parseTreeStr;

function treeDiff
  input list<ParseTree> t1, t2;
  input Integer nTokens "The number of tokens in the larger tree; used to allocate arrays. Should be enough with the smaller tree, but there are no additional bounds checks this way.";
  output list<tuple<Diff,list<ParseTree>>> res;
protected
  list<tuple<Diff,list<ParseTree>>> res1, res2;
  ParseTree within1, within2;
  list<ParseTree> t2_updated;
algorithm
  within1 := findWithin(t1);
  within2 := findWithin(t2);
  // If the new file lacks a within that was in the first file, pretend it is there
  // The other option is to preserve within in OMEdit...
  t2_updated := match (within1,within2)
    case (EMPTY(), EMPTY()) then t2;
    case (_, EMPTY()) then within1::t2;
    else t2;
  end match;
  res := treeDiffWork1(t1, t2_updated, nTokens);
end treeDiff;

partial function CmpParseTreeFunc
  input ParseTree t1, t2;
  output Boolean b;
end CmpParseTreeFunc;

function parseTreeNodeStr
  input ParseTree tree;
  output String str;
protected
  Integer i;
algorithm
  i := Print.saveAndClearBuf();
  try
    parseTreeStrWork(tree);
    str := Print.getString();
    Print.restoreBuf(i);
  else
    Print.restoreBuf(i);
    fail();
  end try;
end parseTreeNodeStr;

partial function partialParser
  input list<Token> inTokens;
  input list<ParseTree> inTree;
  output list<Token> tokens = inTokens;
  output list<ParseTree> outTree;
protected
  list<ParseTree> tree = {};
end partialParser;

function stored_definition
  extends partialParser;
protected
  Boolean b;
algorithm
  (tokens, tree, b) := scanOpt(tokens, tree, TokenId.WITHIN);
  if b then
    (tokens, tree, b) := LA1(tokens, tree, First.name);
    if b then
      (tokens, tree) := name(tokens, tree);
    end if;
    (tokens, tree) := scan(tokens, tree, TokenId.SEMICOLON);
    outTree := makeNode(listReverse(tree), label=LEAF(makeToken(TokenId.IDENT, "$within")))::{};
    tree := {};
  else
    outTree := {};
  end if;

  (tokens, tree, b) := LA1(tokens, tree, First.class_definition);
  while b loop
    (tokens, tree, ) := scanOpt(tokens, tree, TokenId.FINAL);
    (tokens, tree) := class_definition(tokens, tree);
    (tokens, tree) := scan(tokens, tree, TokenId.SEMICOLON);
    (tokens, tree, b) := LA1(tokens, tree, First.class_definition);
    outTree := makeNode(listReverse(tree))::outTree;
    tree := {};
  end while;
  // Eat trailing whitespace so nothing is stripped
  (tokens, tree) := eatWhitespace(tokens, tree);
  // Do an EOF check
  if not listEmpty(tokens) then
    error(tokens, tree, {});
  end if;
  outTree := makeNode(listReverse(listAppend(tree, listAppend(outTree, inTree))), label=LEAF(makeToken(TokenId.IDENT, "$program")))::{};
end stored_definition;

protected

function class_definition
  extends partialParser;
protected
  ParseTree nodeName;
algorithm
  tree := {};
  (tokens, tree) := scanOpt(tokens, tree, TokenId.ENCAPSULATED);
  (tokens, tree) := class_prefixes(tokens, tree);
  (tokens, tree, nodeName) := class_specifier(tokens, tree);
  outTree := makeNode(listReverse(tree), label=nodeName)::inTree;
end class_definition;

function class_prefixes
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree) := scanOpt(tokens, tree, TokenId.PARTIAL);
  (tokens, tree, id) := peek(tokens, tree);
  _ := match id
    case TokenId.OPERATOR
      algorithm
        (tokens, tree) := consume(tokens, tree);
        (tokens, tree) := LA1(tokens, tree, {TokenId.RECORD, TokenId.FUNCTION}, consume=true);
      then ();
    case TokenId.EXPANDABLE
      algorithm
        (tokens, tree) := consume(tokens, tree);
        (tokens, tree) := scan(tokens, tree, TokenId.CONNECTOR);
      then ();
    case id guard listMember(id, {TokenId.PURE, TokenId.IMPURE})
      algorithm
        (tokens, tree) := consume(tokens, tree);
        (tokens, tree, b) := scanOpt(tokens, tree, TokenId.OPERATOR);
        (tokens, tree) := scanOneOf(tokens, tree, if b then {TokenId.FUNCTION} else {TokenId.FUNCTION, TokenId.RECORD});
      then ();
    else
      algorithm
        (tokens, tree) := scanOneOf(tokens, tree, {TokenId.CLASS, TokenId.MODEL, TokenId.RECORD, TokenId.BLOCK, TokenId.CONNECTOR, TokenId.TYPE, TokenId.PACKAGE, TokenId.FUNCTION, TokenId.OPERATOR});
      then ();
  end match;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end class_prefixes;

function class_specifier
  extends partialParser;
  output ParseTree nodeName;
protected
  TokenId id;
  Boolean b;
algorithm
  tree := inTree;
  (tokens, tree, b) := scanOpt(tokens, tree, TokenId.IDENT);
  nodeName::_ := tree;
  if b then
    (tokens, tree, b) := scanOpt(tokens, tree, TokenId.EQUALS);
    if b then
      (tokens, tree, b) := scanOpt(tokens, tree, TokenId.DER);
      if b then
        (tokens, tree) := scan(tokens, tree, TokenId.LPAR);
        (tokens, tree) := name(tokens, tree);
        (tokens, tree) := scan(tokens, tree, TokenId.COMMA);
        (tokens, tree) := scan(tokens, tree, TokenId.IDENT);
        while true loop
          (tokens, tree, b) := scanOpt(tokens, tree, TokenId.COMMA);
          if not b then
            break;
          end if;
          (tokens, tree) := scan(tokens, tree, TokenId.IDENT);
        end while;
        (tokens, tree) := scan(tokens, tree, TokenId.RPAR);
        (tokens, tree) := comment(tokens, tree);
      else
        (tokens, tree) := short_class_specifier1(tokens, tree);
      end if;
    else
      (tokens, tree) := string_comment(tokens, tree);
      (tokens, tree) := composition(tokens, tree);
      (tokens, tree) := scan(tokens, tree, TokenId.END);
      (tokens, tree) := scan(tokens, tree, TokenId.IDENT);
    end if;
  else
    (tokens, tree) := scan(tokens, tree, TokenId.EXTENDS);
    (tokens, tree) := scan(tokens, tree, TokenId.IDENT);
    (tokens, tree, b) := LA1(tokens, tree, First.class_modification);
    if b then
      (tokens, tree) := class_modification(tokens, tree);
    end if;
    (tokens, tree) := string_comment(tokens, tree);
    (tokens, tree) := composition(tokens, tree);
    (tokens, tree) := scan(tokens, tree, TokenId.END);
    (tokens, tree) := scan(tokens, tree, TokenId.IDENT);
  end if;
  outTree := tree;
end class_specifier;

function short_class_specifier1
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree, b) := scanOpt(tokens, tree, TokenId.ENUMERATION);
  if b then
    (tokens, tree) := scan(tokens, tree, TokenId.LPAR);
    (tokens, tree, b) := scanOpt(tokens, tree, TokenId.COLON);
    if not b then
      while true loop
        (tokens, tree) := enumeration_literal(tokens, tree);
        (tokens, tree, b) := scanOpt(tokens, tree, TokenId.COMMA);
        if not b then
          break;
        end if;
      end while;
    end if;
    (tokens, tree) := scan(tokens, tree, TokenId.RPAR);
  else
    (tokens, tree) := base_prefix(tokens, tree);
    (tokens, tree) := name(tokens, tree);
    (tokens, tree, b) := LA1(tokens, tree, {TokenId.LBRACK});
    if b then
      (tokens, tree) := array_subscripts(tokens, tree);
    end if;
    (tokens, tree, b) := LA1(tokens, tree, First.class_modification);
    if b then
      (tokens, tree) := class_modification(tokens, tree);
    end if;
  end if;
  (tokens, tree) := comment(tokens, tree);
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end short_class_specifier1;

function enumeration_literal
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree) := scan(tokens, tree, TokenId.IDENT);
  (tokens, tree) := comment(tokens, tree);
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end enumeration_literal;

function composition
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree) := element_list(tokens, tree);
  while true loop
    (tokens, tree, b) := LA1(tokens, tree, {TokenId.PROTECTED, TokenId.PUBLIC, TokenId.INITIAL, TokenId.EQUATION, TokenId.ALGORITHM});
    if not b then
      break;
    end if;
    (tokens, tree, b) := LA1(tokens, tree, {TokenId.PROTECTED, TokenId.PUBLIC}, consume=true);
    if b then
      (tokens, tree) := element_list(tokens, tree);
    else
      (tokens, tree) := scanOpt(tokens, tree, TokenId.INITIAL);
      (tokens, tree, b) := LA1(tokens, tree, {TokenId.ALGORITHM});
      if b then
        (tokens, tree) := algorithm_section(tokens, tree);
      else
        (tokens, tree) := equation_section(tokens, tree);
      end if;
    end if;
  end while;
  (tokens, tree, b) := scanOpt(tokens, tree, TokenId.EXTERNAL);
  if b then
    (tokens, tree) := scanOpt(tokens, tree, TokenId.STRING); // language
    (tokens, tree) := external_function_call(tokens, tree);
    (tokens, tree, b) := LA1(tokens, tree, First._annotation);
    if b then
      (tokens, tree) := _annotation(tokens, tree);
    end if;
    (tokens, tree) := scan(tokens, tree, TokenId.SEMICOLON);
  end if;

  (tokens, tree, b) := LA1(tokens, tree, First._annotation);
  if b then
    (tokens, tree) := _annotation(tokens, tree);
    (tokens, tree) := scan(tokens, tree, TokenId.SEMICOLON);
  end if;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end composition;

function external_function_call
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree, b) := LAk(tokens, tree, {{TokenId.IDENT},{TokenId.LPAR}});
  if not b then
    (tokens, tree) := component_reference(tokens, tree);
    (tokens, tree) := scan(tokens, tree, TokenId.EQUALS);
  end if;
  (tokens, tree) := scan(tokens, tree, TokenId.IDENT);
  (tokens, tree) := scan(tokens, tree, TokenId.LPAR);
  (tokens, tree) := expression_list(tokens, tree);
  (tokens, tree) := scan(tokens, tree, TokenId.RPAR);
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end external_function_call;

function algorithm_section
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree) := scanOpt(tokens, tree, TokenId.INITIAL);
  (tokens, tree) := scan(tokens, tree, TokenId.ALGORITHM);
  (tokens, tree) := statement_list(tokens, tree);
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end algorithm_section;

function statement
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree, id) := peek(tokens, tree);
  if id==TokenId.BREAK or id==TokenId.RETURN then
    (tokens, tree) := consume(tokens, tree);
  elseif listMember(id, First.component_reference) then
    (tokens, tree) := component_reference(tokens, tree);
    (tokens, tree, b) := scanOpt(tokens, tree, TokenId.ASSIGN);
    if b then
      (tokens, tree) := expression(tokens, tree);
    else
      (tokens, tree) := function_call_args(tokens, tree);
    end if;
  elseif id==TokenId.IF then
    (tokens, tree) := consume(tokens, tree);
    (tokens, tree) := expression(tokens, tree);
    (tokens, tree) := scan(tokens, tree, TokenId.THEN);
    (tokens, tree) := statement_list(tokens, tree);
    while true loop
      (tokens, tree, b) := scanOpt(tokens, tree, TokenId.ELSEIF);
      if not b then
        break;
      end if;
      (tokens, tree) := expression(tokens, tree);
      (tokens, tree) := scan(tokens, tree, TokenId.THEN);
      (tokens, tree) := statement_list(tokens, tree);
    end while;
    (tokens, tree, b) := scanOpt(tokens, tree, TokenId.ELSE);
    if b then
      (tokens, tree) := statement_list(tokens, tree);
    end if;
    (tokens, tree) := scan(tokens, tree, TokenId.END);
    (tokens, tree) := scan(tokens, tree, TokenId.IF);
  elseif id==TokenId.WHEN then
    (tokens, tree) := consume(tokens, tree);
    (tokens, tree) := expression(tokens, tree);
    (tokens, tree) := scan(tokens, tree, TokenId.THEN);
    (tokens, tree) := statement_list(tokens, tree);
    while true loop
      (tokens, tree, b) := scanOpt(tokens, tree, TokenId.ELSEWHEN);
      if not b then
        break;
      end if;
      (tokens, tree) := expression(tokens, tree);
      (tokens, tree) := scan(tokens, tree, TokenId.THEN);
      (tokens, tree) := statement_list(tokens, tree);
    end while;
    (tokens, tree) := scan(tokens, tree, TokenId.END);
    (tokens, tree) := scan(tokens, tree, TokenId.WHEN);
  elseif id==TokenId.FOR then
    (tokens, tree) := consume(tokens, tree);
    (tokens, tree) := for_indices(tokens, tree);
    (tokens, tree) := scan(tokens, tree, TokenId.LOOP);
    (tokens, tree) := statement_list(tokens, tree);
    (tokens, tree) := scan(tokens, tree, TokenId.END);
    (tokens, tree) := scan(tokens, tree, TokenId.FOR);
  elseif id==TokenId.WHILE then
    (tokens, tree) := consume(tokens, tree);
    (tokens, tree) := expression(tokens, tree);
    (tokens, tree) := scan(tokens, tree, TokenId.LOOP);
    (tokens, tree) := statement_list(tokens, tree);
    (tokens, tree) := scan(tokens, tree, TokenId.END);
    (tokens, tree) := scan(tokens, tree, TokenId.WHILE);
  else
    (tokens, tree) := expression(tokens, tree);
    (tokens, tree, b) := scanOpt(tokens, tree, TokenId.ASSIGN);
    if b then
      (tokens, tree) := expression(tokens, tree);
    end if;
  end if;
  (tokens, tree) := comment(tokens, tree);
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end statement;

function statement_list
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  outTree := {};
  while true loop
    (tokens, tree, b) := LA1(tokens, tree, Follow.statement_equation);
    if b then
      break;
    end if;
    (tokens, tree) := statement(tokens, tree);
    (tokens, tree) := scan(tokens, tree, TokenId.SEMICOLON);

    outTree := makeNode(listReverse(tree))::outTree;
    tree := {};
  end while;
  outTree := listAppend(tree, listAppend(outTree, inTree));
end statement_list;

function equation_section
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree) := scanOpt(tokens, tree, TokenId.INITIAL);
  (tokens, tree) := scan(tokens, tree, TokenId.EQUATION);
  (tokens, tree) := equation_list(tokens, tree);
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end equation_section;

function _equation
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree, id) := peek(tokens, tree);
  if id==TokenId.IF then
    (tokens, tree) := consume(tokens, tree);
    (tokens, tree) := expression(tokens, tree);
    (tokens, tree) := scan(tokens, tree, TokenId.THEN);
    (tokens, tree) := equation_list(tokens, tree);
    while true loop
      (tokens, tree, b) := scanOpt(tokens, tree, TokenId.ELSEIF);
      if not b then
        break;
      end if;
      (tokens, tree) := expression(tokens, tree);
      (tokens, tree) := scan(tokens, tree, TokenId.THEN);
      (tokens, tree) := equation_list(tokens, tree);
    end while;
    (tokens, tree, b) := scanOpt(tokens, tree, TokenId.ELSE);
    if b then
      (tokens, tree) := equation_list(tokens, tree);
    end if;
    (tokens, tree) := scan(tokens, tree, TokenId.END);
    (tokens, tree) := scan(tokens, tree, TokenId.IF);
  elseif id==TokenId.WHEN then
    (tokens, tree) := consume(tokens, tree);
    (tokens, tree) := expression(tokens, tree);
    (tokens, tree) := scan(tokens, tree, TokenId.THEN);
    (tokens, tree) := equation_list(tokens, tree);
    while true loop
      (tokens, tree, b) := scanOpt(tokens, tree, TokenId.ELSEWHEN);
      if not b then
        break;
      end if;
      (tokens, tree) := expression(tokens, tree);
      (tokens, tree) := scan(tokens, tree, TokenId.THEN);
      (tokens, tree) := equation_list(tokens, tree);
    end while;
    (tokens, tree) := scan(tokens, tree, TokenId.END);
    (tokens, tree) := scan(tokens, tree, TokenId.WHEN);
  elseif id==TokenId.FOR then
    (tokens, tree) := consume(tokens, tree);
    (tokens, tree) := for_indices(tokens, tree);
    (tokens, tree) := scan(tokens, tree, TokenId.LOOP);
    (tokens, tree) := equation_list(tokens, tree);
    (tokens, tree) := scan(tokens, tree, TokenId.END);
    (tokens, tree) := scan(tokens, tree, TokenId.FOR);
  elseif id==TokenId.CONNECT then
    (tokens, tree) := consume(tokens, tree);
    (tokens, tree) := scan(tokens, tree, TokenId.LPAR);
    (tokens, tree) := component_reference(tokens, tree);
    (tokens, tree) := scan(tokens, tree, TokenId.COMMA);
    (tokens, tree) := component_reference(tokens, tree);
    (tokens, tree) := scan(tokens, tree, TokenId.RPAR);
  else
    (tokens, tree) := expression(tokens, tree);
    (tokens, tree, b) := scanOpt(tokens, tree, TokenId.EQUALS);
    if b then
      (tokens, tree) := expression(tokens, tree);
    end if;
  end if;
  (tokens, tree) := comment(tokens, tree);
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end _equation;

function equation_list
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  outTree := {};
  while true loop
    (tokens, tree, b) := LA1(tokens, tree, Follow.statement_equation);
    if b then
      break;
    end if;
    (tokens, tree) := _equation(tokens, tree);
    (tokens, tree) := scan(tokens, tree, TokenId.SEMICOLON);

    outTree := makeNode(listReverse(tree))::outTree;
    tree := {};
  end while;
  outTree := listAppend(tree, listAppend(outTree, inTree));
end equation_list;

function element_list
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  outTree := {};
  while true loop
    (tokens, tree, b) := LA1(tokens, tree, First.element);
    if not b then
      break;
    end if;
    (tokens, tree) := element(tokens, tree);
    (tokens, tree) := scan(tokens, tree, TokenId.SEMICOLON);

    outTree := makeNode(listReverse(tree))::outTree;
    tree := {};
  end while;
  outTree := listAppend(tree, listAppend(outTree, inTree));
end element_list;

function element
  extends partialParser;
protected
  TokenId id;
  Boolean b,b1;
algorithm
  (tokens, tree, id) := peek(tokens, tree);
  _ := match id
    case TokenId.IMPORT
      algorithm
        (tokens, tree) := import_clause(tokens, tree);
      then ();
    case TokenId.EXTENDS
      algorithm
        (tokens, tree) := extends_clause(tokens, tree);
      then ();
    else
      algorithm
        (tokens, tree) := scanOpt(tokens, tree, TokenId.REDECLARE);
        (tokens, tree) := scanOpt(tokens, tree, TokenId.FINAL);
        (tokens, tree) := scanOpt(tokens, tree, TokenId.INNER);
        (tokens, tree) := scanOpt(tokens, tree, TokenId.OUTER);
        (tokens, tree, b1) := scanOpt(tokens, tree, TokenId.REPLACEABLE);
        (tokens, tree, b) := LA1(tokens, tree, First.class_definition);
        if b then
          (tokens, tree) := class_definition(tokens, tree);
        else
          (tokens, tree) := component_clause(tokens, tree);
        end if;
        if b1 then
          (tokens, tree, b) := LA1(tokens, tree, {TokenId.CONSTRAINEDBY});
          if b then
            (tokens, tree) := constraining_clause(tokens, tree);
            (tokens, tree) := comment(tokens, tree);
          end if;
        end if;
      then ();
  end match;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end element;

function constraining_clause
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree) := scan(tokens, tree, TokenId.CONSTRAINEDBY);
  (tokens, tree) := name(tokens, tree);
  (tokens, tree, b) := LA1(tokens, tree, First.class_modification);
  if b then
    (tokens, tree) := class_modification(tokens, tree);
  end if;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end constraining_clause;

function component_clause
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree) := type_prefix(tokens, tree);
  (tokens, tree) := type_specifier(tokens, tree);
  (tokens, tree, b) := LA1(tokens, tree, {TokenId.LBRACK});
  if b then
    (tokens, tree) := array_subscripts(tokens, tree);
  end if;
  (tokens, tree) := component_list(tokens, tree);
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end component_clause;

function import_clause
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree) := scan(tokens, tree, TokenId.IMPORT);
  (tokens, tree, b) := LAk(tokens, tree, {{TokenId.IDENT}, {TokenId.EQUALS}});
  if b then
    (tokens, tree) := scan(tokens, tree, TokenId.IDENT);
    (tokens, tree) := scan(tokens, tree, TokenId.EQUALS);
    (tokens, tree) := name(tokens, tree);
  else
    (tokens, tree) := name(tokens, tree);
    (tokens, tree, b) := scanOpt(tokens, tree, TokenId.STAR_EW);
    if not b then
      (tokens, tree, b) := scanOpt(tokens, tree, TokenId.DOT);
      if b then
        (tokens, tree) := scan(tokens, tree, TokenId.LBRACE);
        (tokens, tree) := scan(tokens, tree, TokenId.IDENT);
        while true loop
          (tokens, tree, b) := scanOpt(tokens, tree, TokenId.COMMA);
          if not b then
            break;
          end if;
          (tokens, tree, b) := scanOpt(tokens, tree, TokenId.IDENT);
        end while;
        (tokens, tree) := scan(tokens, tree, TokenId.RBRACE);
      end if;
    end if;
  end if;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end import_clause;

function type_specifier = name;
function base_prefix = type_prefix;

function type_prefix
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree) := LA1(tokens, tree, {TokenId.FLOW, TokenId.STREAM}, consume=true);
  (tokens, tree) := LA1(tokens, tree, {TokenId.DISCRETE, TokenId.PARAMETER, TokenId.CONSTANT}, consume=true);
  (tokens, tree) := LA1(tokens, tree, {TokenId.INPUT, TokenId.OUTPUT}, consume=true);
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end type_prefix;

function array_subscripts
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree) := scan(tokens, tree, TokenId.LBRACK);
  (tokens, tree) := subscript(tokens, tree);
  while true loop
    (tokens, tree, b) := scanOpt(tokens, tree, TokenId.COMMA);
    if not b then
      break;
    end if;
    (tokens, tree) := subscript(tokens, tree);
  end while;
  (tokens, tree) := scan(tokens, tree, TokenId.RBRACK);
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end array_subscripts;

function subscript
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree, b) := scanOpt(tokens, tree, TokenId.COLON);
  if not b then
    (tokens, tree) := expression(tokens, tree);
  end if;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end subscript;

function component_list
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree) := component_declaration(tokens, tree);
  while true loop
    (tokens, tree, b) := scanOpt(tokens, tree, TokenId.COMMA);
    if not b then
      break;
    end if;
    (tokens, tree) := component_declaration(tokens, tree);
  end while;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end component_list;

function component_declaration
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree) := declaration(tokens, tree);
  (tokens, tree, b) := scanOpt(tokens, tree, TokenId.IF);
  if b then
    (tokens, tree) := expression(tokens, tree);
  end if;
  // print("component_declaration: comment1 "+topTokenStr(tokens)+"\n");
  (tokens, tree) := comment(tokens, tree);
  // print("component_declaration: comment2 "+topTokenStr(tokens)+"\n");
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end component_declaration;

function declaration
  extends partialParser;
  output ParseTree nodeName;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree) := scan(tokens, tree, TokenId.IDENT);
  nodeName::_ := tree;
  (tokens, tree, b) := LA1(tokens, tree, {TokenId.LBRACK});
  if b then
    (tokens, tree) := array_subscripts(tokens, tree);
  end if;
  (tokens, tree, b) := LA1(tokens, tree, First.modification);
  // print("declaration has modification?: "+String(b)+"\n");
  if b then
    // print("before mod: "+topTokenStr(tokens)+"\n");
    (tokens, tree) := modification(tokens, tree);
    // print("after mod: "+topTokenStr(tokens)+"\n");
  end if;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end declaration;

function component_clause1
  extends partialParser;
  output ParseTree nodeName;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree) := type_prefix(tokens, tree);
  (tokens, tree) := type_specifier(tokens, tree);
  (tokens, tree, nodeName) := component_declaration1(tokens, tree);
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end component_clause1;

function component_declaration1
  extends partialParser;
  output ParseTree nodeName;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree, nodeName) := declaration(tokens, tree);
  (tokens, tree) := comment(tokens, tree);
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end component_declaration1;

function extends_clause
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree) := scan(tokens, tree, TokenId.EXTENDS);
  (tokens, tree) := name(tokens, tree);
  (tokens, tree, b) := LA1(tokens, tree, First.class_modification);
  if b then
    (tokens, tree) := class_modification(tokens, tree);
  end if;
  (tokens, tree, b) := LA1(tokens, tree, First._annotation);
  if b then
    // (tokens, tree) := _annotation(tokens, tree);
  end if;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end extends_clause;

function class_modification
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree) := scan(tokens, tree, TokenId.LPAR);
  (tokens, tree, b) := LA1(tokens, tree, First.argument);
  if b then
    (tokens, tree) := argument_list(tokens, tree);
  end if;
  (tokens, tree) := scan(tokens, tree, TokenId.RPAR);
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end class_modification;

function argument_list
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree) := argument(tokens, tree);
  b := true;
  while b loop
    (tokens, tree, b) := scanOpt(tokens, tree, TokenId.COMMA);
    if b then
      (tokens, tree) := argument(tokens, tree);
    end if;
  end while;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end argument_list;

function argument
  extends partialParser;
protected
  TokenId id;
  Boolean b;
  ParseTree nodeName;
algorithm
  (tokens, tree, b) := LA1(tokens, tree, {TokenId.REDECLARE});
  if b then
    (tokens, tree, nodeName) := element_redeclaration(tokens, tree);
  else
    (tokens, tree, nodeName) := element_modification_or_replaceable(tokens, tree);
  end if;
  nodeName := makeNode(listReverse(tree), label=nodeName);
  outTree := nodeName::inTree;
end argument;

function element_redeclaration
  extends partialParser;
  output ParseTree nodeName;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree) := scan(tokens, tree, TokenId.REDECLARE);
  (tokens, tree) := scanOpt(tokens, tree, TokenId.EACH);
  (tokens, tree) := scanOpt(tokens, tree, TokenId.FINAL);
  (tokens, tree, b) := LA1(tokens, tree, {TokenId.REPLACEABLE});
  if b then
    (tokens, tree) := element_replaceable(tokens, tree);
  else
    (tokens, tree, b) := LA1(tokens, tree, First.class_prefixes);
    if b then
      (tokens, tree, nodeName) := short_class_definition(tokens, tree);
    else
      (tokens, tree, nodeName) := component_clause1(tokens, tree);
    end if;
  end if;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end element_redeclaration;

function short_class_definition
  extends partialParser;
  output ParseTree nodeName;
protected
  TokenId id;
  Boolean b;
  Token nodeNameT;
algorithm
  (tokens, tree) := class_prefixes(tokens, tree);
  (tokens, tree) := scan(tokens, tree, TokenId.IDENT);
  nodeName::_ := tree;
  (tokens, tree) := scan(tokens, tree, TokenId.EQUALS);
  (tokens, tree) := short_class_specifier1(tokens, tree);
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end short_class_definition;

function element_modification_or_replaceable
  extends partialParser;
  output ParseTree nodeName;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree) := scanOpt(tokens, tree, TokenId.EACH);
  (tokens, tree) := scanOpt(tokens, tree, TokenId.FINAL);
  (tokens, tree, b) := LA1(tokens, tree, {TokenId.REPLACEABLE});
  if b then
    (tokens, tree, nodeName) := element_replaceable(tokens, tree);
  else
    (tokens, tree, nodeName) := element_modification(tokens, tree);
  end if;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end element_modification_or_replaceable;

function element_replaceable
  extends partialParser;
  output ParseTree nodeName;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree) := scan(tokens, tree, TokenId.REPLACEABLE);
  (tokens, tree, b) := LA1(tokens, tree, First.component_clause);
  if b then
    (tokens, tree, nodeName) := component_clause1(tokens, tree);
  else
    (tokens, tree, nodeName) := short_class_definition(tokens, tree);
  end if;
  (tokens, tree, b) := LA1(tokens, tree, {TokenId.CONSTRAINEDBY});
  if b then
    (tokens, tree) := constraining_clause(tokens, tree);
  end if;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end element_replaceable;

function element_modification
  extends partialParser;
  output ParseTree nodeName;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree) := name(tokens, tree);
  nodeName::_ := tree;
  (tokens, tree, b) := LA1(tokens, tree, First.modification);
  if b then
    (tokens, tree) := modification(tokens, tree);
  end if;
  (tokens, tree) := string_comment(tokens, tree);
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end element_modification;

function modification
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree, b) := LA1(tokens, tree, First.class_modification);
  if b then
    (tokens, tree) := class_modification(tokens, tree);
    (tokens, tree) := eatWhitespace(tokens, tree);
    (tokens, tree, b) := scanOpt(tokens, tree, TokenId.EQUALS);
    (tokens, tree) := eatWhitespace(tokens, tree);
    if b then
      (tokens, tree) := expression(tokens, tree);
    end if;
  else
    (tokens, tree) := eatWhitespace(tokens, tree);
    (tokens, tree) := scanOneOf(tokens, tree, {TokenId.EQUALS, TokenId.ASSIGN});
    (tokens, tree) := eatWhitespace(tokens, tree);
    (tokens, tree) := expression(tokens, tree);
  end if;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end modification;

function expression_list
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  while true loop
    (tokens, tree) := expression(tokens, tree);
    (tokens, tree, b) := scanOpt(tokens, tree, TokenId.COMMA);
    if not b then
      break;
    end if;
  end while;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end expression_list;

function expression
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree, b) := scanOpt(tokens, tree, TokenId.IF);
  if b then
    (tokens, tree) := expression(tokens, tree);
    (tokens, tree) := scan(tokens, tree, TokenId.THEN);
    (tokens, tree) := expression(tokens, tree);
    while true loop
      (tokens, tree, b) := scanOpt(tokens, tree, TokenId.ELSEIF);
      if not b then
        break;
      end if;
      (tokens, tree) := expression(tokens, tree);
      (tokens, tree) := scan(tokens, tree, TokenId.THEN);
      (tokens, tree) := expression(tokens, tree);
    end while;
    (tokens, tree) := scan(tokens, tree, TokenId.ELSE);
    (tokens, tree) := expression(tokens, tree);
  else
    (tokens, tree) := simple_expression(tokens, tree);
  end if;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end expression;

function simple_expression
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree) := logical_expression(tokens, tree);
  (tokens, tree, b) := scanOpt(tokens, tree, TokenId.COLON);
  if b then
    (tokens, tree) := logical_expression(tokens, tree);
    (tokens, tree, b) := scanOpt(tokens, tree, TokenId.COLON);
    if b then
      (tokens, tree) := logical_expression(tokens, tree);
    end if;
  end if;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end simple_expression;

function logical_expression
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree) := logical_term(tokens, tree);
  while true loop
    (tokens, tree, b) := scanOpt(tokens, tree, TokenId.OR);
    if not b then
      break;
    end if;
    (tokens, tree) := logical_term(tokens, tree);
  end while;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end logical_expression;

function logical_term
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree) := logical_factor(tokens, tree);
  while true loop
    (tokens, tree, b) := scanOpt(tokens, tree, TokenId.AND);
    if not b then
      break;
    end if;
    (tokens, tree) := logical_factor(tokens, tree);
  end while;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end logical_term;

function logical_factor
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree, b) := scanOpt(tokens, tree, TokenId.NOT);
  (tokens, tree) := relation(tokens, tree);
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end logical_factor;

function relation
  extends partialParser;
protected
  TokenId id;
  Boolean b;
  constant list<TokenId> rel_op = {TokenId.LESS, TokenId.LESSEQ, TokenId.GREATER, TokenId.GREATEREQ, TokenId.EQEQ, TokenId.LESSGT};
algorithm
  (tokens, tree) := arithmetic_expression(tokens, tree);
  while true loop
    (tokens, tree, b) := LA1(tokens, tree, rel_op, consume=true);
    if not b then
      break;
    end if;
    (tokens, tree) := arithmetic_expression(tokens, tree);
  end while;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end relation;

function arithmetic_expression
  extends partialParser;
protected
  TokenId id;
  Boolean b;
  constant list<TokenId> add_op = {TokenId.PLUS, TokenId.MINUS, TokenId.PLUS_EW, TokenId.MINUS_EW};
algorithm
  (tokens, tree) := LA1(tokens, tree, add_op, consume=true);
  (tokens, tree) := term(tokens, tree);
  while true loop
    (tokens, tree, b) := LA1(tokens, tree, add_op, consume=true);
    if not b then
      break;
    end if;
    (tokens, tree) := term(tokens, tree);
  end while;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end arithmetic_expression;

function term
  extends partialParser;
protected
  TokenId id;
  Boolean b;
  constant list<TokenId> mul_op = {TokenId.STAR, TokenId.STAR_EW, TokenId.SLASH, TokenId.SLASH_EW};
algorithm
  (tokens, tree) := factor(tokens, tree);
  while true loop
    (tokens, tree, b) := LA1(tokens, tree, mul_op, consume=true);
    if not b then
      break;
    end if;
    (tokens, tree) := factor(tokens, tree);
  end while;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end term;

function factor
  extends partialParser;
protected
  TokenId id;
  Boolean b;
  constant list<TokenId> pow_op = {TokenId.POWER, TokenId.POWER_EW};
algorithm
  (tokens, tree) := primary(tokens, tree);
  while true loop
    (tokens, tree, b) := LA1(tokens, tree, pow_op, consume=true);
    if not b then
      break;
    end if;
    (tokens, tree) := primary(tokens, tree);
  end while;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end factor;

function primary
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree, b) := LA1(tokens, tree, {TokenId.UNSIGNED_INTEGER, TokenId.UNSIGNED_REAL, TokenId.FALSE, TokenId.TRUE, TokenId.END, TokenId.STRING});
  if b then
    (tokens, tree) := consume(tokens, tree);
    outTree := makeNodePrependTree(listReverse(tree), inTree);
    return;
  end if;
  (tokens, tree, id) := peek(tokens, tree);
  if id==TokenId.LPAR then
    (tokens, tree) := output_expression_list(tokens, tree);
  elseif id==TokenId.LBRACE then
    (tokens, tree) := scan(tokens, tree, TokenId.LBRACE);
    (tokens, tree, b) := LA1(tokens, tree, {TokenId.RBRACE}); // Easier than checking First(expression), etc
    if not b then
      (tokens, tree) := function_arguments(tokens, tree);
    end if;
    (tokens, tree) := scan(tokens, tree, TokenId.RBRACE);
  elseif id==TokenId.LBRACK then
    (tokens, tree) := consume(tokens, tree);
    (tokens, tree) := expression_list(tokens, tree);
    while true loop
      (tokens, tree, b) := scanOpt(tokens, tree, TokenId.SEMICOLON);
      if not b then
        break;
      end if;
      (tokens, tree) := expression_list(tokens, tree);
    end while;
    (tokens, tree) := scan(tokens, tree, TokenId.RBRACK);
  elseif listMember(id, {TokenId.DER, TokenId.INITIAL}) then
    (tokens, tree) := consume(tokens, tree);
    (tokens, tree, b) := LA1(tokens, tree, {TokenId.LPAR});
    if b then
      (tokens, tree) := function_call_args(tokens, tree);
    end if;
  elseif listMember(id, {TokenId.DOT, TokenId.IDENT}) then
    (tokens, tree) := component_reference(tokens, tree);
    (tokens, tree, b) := LA1(tokens, tree, {TokenId.LPAR});
    if b then
      (tokens, tree) := function_call_args(tokens, tree);
    end if;
  else
    error(tokens, tree, {});
  end if;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end primary;

function function_call_args
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree) := scan(tokens, tree, TokenId.LPAR);
  (tokens, tree, b) := scanOpt(tokens, tree, TokenId.RPAR); // Easier than checking First.expression, etc
  if not b then
    (tokens, tree) := function_arguments(tokens, tree);
    (tokens, tree) := scan(tokens, tree, TokenId.RPAR);
  end if;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end function_call_args;

function function_arguments
  extends partialParser;
protected
  TokenId id;
  Boolean b;
  list<ParseTree> tree2;
algorithm
  (tokens, tree, b) := LAk(tokens, tree, {{TokenId.IDENT}, {TokenId.EQUALS}});
  if b then
    (tokens, tree) := named_arguments(tokens, tree);
  else
    (tokens, tree) := function_argument(tokens, tree);
    (tokens, tree2, b) := scanOpt(tokens, {}, TokenId.COMMA);
    if b then
      tree := makeNode(listReverse(tree2))::tree;
      (tokens, tree) := function_arguments(tokens, tree);
    else
      (tokens, tree, b) := scanOpt(tokens, tree, TokenId.FOR);
      if b then
        (tokens, tree) := for_indices(tokens, tree);
      end if;
    end if;
  end if;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end function_arguments;

function function_argument
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree, b) := scanOpt(tokens, tree, TokenId.FUNCTION);
  if b then
    (tokens, tree) := name(tokens, tree);
    (tokens, tree) := scan(tokens, tree, TokenId.LPAR);
    (tokens, tree, b) := LA1(tokens, tree, {TokenId.IDENT});
    if b then
      (tokens, tree) := named_arguments(tokens, tree);
    end if;
    (tokens, tree) := scan(tokens, tree, TokenId.RPAR);
  else
    (tokens, tree) := expression(tokens, tree);
  end if;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end function_argument;

function named_arguments
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree) := named_argument(tokens, tree);
  while true loop
    (tokens, tree, b) := scanOpt(tokens, tree, TokenId.COMMA);
    if not b then
      break;
    end if;
    (tokens, tree) := named_argument(tokens, tree);
  end while;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end named_arguments;

function named_argument
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree) := scan(tokens, tree, TokenId.IDENT);
  (tokens, tree) := scan(tokens, tree, TokenId.EQUALS);
  (tokens, tree) := expression(tokens, tree);
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end named_argument;

function for_indices
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree) := for_index(tokens, tree);
  while true loop
    (tokens, tree, b) := scanOpt(tokens, tree, TokenId.COMMA);
    if not b then
      break;
    end if;
    (tokens, tree) := for_index(tokens, tree);
  end while;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end for_indices;

function for_index
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree) := scan(tokens, tree, TokenId.IDENT);
  (tokens, tree, b) := scanOpt(tokens, tree, TokenId.IN);
  if b then
    (tokens, tree) := expression(tokens, tree);
  end if;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end for_index;

function string_comment
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree, b) := scanOpt(tokens, tree, TokenId.STRING);
  while b loop
    (tokens, tree, b) := scanOpt(tokens, tree, TokenId.PLUS);
    if b then
      (tokens, tree) := scan(tokens, tree, TokenId.STRING);
    end if;
  end while;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end string_comment;

function output_expression_list
  extends partialParser;
protected
  TokenId id;
  Boolean b1, b2;
algorithm
  (tokens, tree) := scan(tokens, tree, TokenId.LPAR);
  while true loop
    (tokens, tree, b1) := scanOpt(tokens, tree, TokenId.COMMA);
    (tokens, tree, b2) := scanOpt(tokens, tree, TokenId.RPAR);
    if b2 then
      break;
    end if;
    if not b1 then
      (tokens, tree) := expression(tokens, tree);
    end if;
  end while;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end output_expression_list;

function name
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree) := scanOpt(tokens, tree, TokenId.DOT);
  (tokens, tree) := scan(tokens, tree, TokenId.IDENT);
  while true loop
    (tokens, tree, b) := scanOpt(tokens, tree, TokenId.DOT);
    if not b then
      break;
    end if;
    (tokens, tree) := scan(tokens, tree, TokenId.IDENT);
  end while;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end name;

function component_reference
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree) := scanOpt(tokens, tree, TokenId.DOT);
  while true loop
    (tokens, tree) := scan(tokens, tree, TokenId.IDENT);
    (tokens, tree, b) := LA1(tokens, tree, {TokenId.LBRACK});
    if b then
      (tokens, tree) := array_subscripts(tokens, tree);
    end if;
    (tokens, tree, b) := scanOpt(tokens, tree, TokenId.DOT);
    if not b then
      break;
    end if;
  end while;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end component_reference;

function comment
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  (tokens, tree) := string_comment(tokens, tree);
  (tokens, tree, b) := LA1(tokens, tree, First._annotation);
  if b then
    (tokens, tree) := _annotation(tokens, tree);
  end if;
  outTree := makeNodePrependTree(listReverse(tree), inTree);
end comment;

function _annotation
  extends partialParser;
protected
  TokenId id;
  Boolean b;
algorithm
  tree := {};
  (tokens, tree) := scan(tokens, tree, TokenId.ANNOTATION);
  (tokens, tree) := class_modification(tokens, tree);
  outTree := makeNode(listReverse(tree), label=LEAF(makeToken(TokenId.IDENT, "annotation")))::inTree;
end _annotation;

protected

function findWithin
  input list<ParseTree> tree;
  output ParseTree w=EMPTY();
protected
  Token tok, tok2;
  TokenId id;
  list<ParseTree> rest, rest2;
algorithm
  w := match tree
    case NODE(label=LEAF(token=tok), nodes=(w as NODE(label=LEAF(token=tok2)))::rest)::rest2 guard tokenContent(tok)=="$program" and tokenContent(tok2)=="$within"
      then w;
    else EMPTY();
  end match;
end findWithin;

function treeDiffWork1
  input list<ParseTree> t1, t2;
  input Integer nTokens "The number of tokens in the larger tree; used to allocate arrays. Should be enough with the smaller tree, but there are no additional bounds checks this way.";
  output list<tuple<Diff,list<ParseTree>>> res;
protected
  array<Token> diffSubtreeWorkArray1, diffSubtreeWorkArray2 "Used to handle diff of trees without using stack space or new allocations for every step";
  list<ParseTree> tree;
algorithm
  // Handle empty input
  if listEmpty(t1) then
    res := {(Diff.Add, t2)};
    return;
  elseif listEmpty(t2) then
    res := {(Diff.Delete, t1)};
    return;
  end if;
  diffSubtreeWorkArray1 := MetaModelica.Dangerous.arrayCreateNoInit(nTokens, LexerModelicaDiff.noToken);
  diffSubtreeWorkArray2 := MetaModelica.Dangerous.arrayCreateNoInit(nTokens, LexerModelicaDiff.noToken);
  if parseTreeEq(makeNode(t1), makeNode(t2), diffSubtreeWorkArray1=diffSubtreeWorkArray1, diffSubtreeWorkArray2=diffSubtreeWorkArray2) then
    // We need to do one check here since we assume the trees are different in the diff algorithm...
    res := {(Diff.Equal, t1)};
    return;
  end if;
  res := treeDiffWork(t1, t2, 1, function parseTreeEq(diffSubtreeWorkArray1=diffSubtreeWorkArray1, diffSubtreeWorkArray2=diffSubtreeWorkArray2));
end treeDiffWork1;

function treeDiffWork
  input list<ParseTree> t1, t2;
  input Integer depth;
  input CmpParseTreeFunc compare;
  output list<tuple<Diff,list<ParseTree>>> res, resLocal;
protected
  list<ParseTree> before, middle, after, addedTrees, deletedTrees;
  Integer nadd, ndel;
  ParseTree addedTree, deletedTree, addedLabel, deletedLabel;
  Boolean addedBeforeDeleted, joinTrees;
  tuple<Diff,list<ParseTree>> diff1;
algorithm
  // Speed-up. No deep compare for single nodes...
  _ := match (t1, t2)
    case ({NODE(nodes=before)}, {NODE(nodes=after)})
      algorithm
        res := treeDiffWork(before, after, depth, compare);
        return;
      then ();
    case ({NODE(nodes=before)}, _)
      algorithm
        res := treeDiffWork(before, t2, depth, compare);
        return;
      then ();
    case (_, {NODE(nodes=after)})
      algorithm
        res := treeDiffWork(t1, after, depth, compare);
        return;
      then ();
    else ();
  end match;
  if debug then
    print("Do diff at depth="+String(depth)+", len(t1)="+String(listLength(t1))+", len(t2)="+String(listLength(t2))+"\n");
    print("top t1="+firstTokenDebugStr(t1)+"\n");
    print("top t2="+firstTokenDebugStr(t2)+"\n");
    print("all t1="+parseTreeStr(t1)+"\n");
    print("all t2="+parseTreeStr(t2)+"\n");
  end if;
  res := diff(t1, t2, compare, parseTreeIsWhitespace, parseTreeNodeStr);
  (nadd, ndel) := countDiffAddDelete(res);
  if nadd > 1 then
    res := fixMoveOperations(res, compare);
    (nadd, ndel) := countDiffAddDelete(res);
  end if;
  if debug then
    print("nadd: " + String(nadd) + " ndel: " + String(ndel) + "\n");
    print(DiffAlgorithm.printDiffXml(res, parseTreeNodeStr) + "\n");
  end if;
  if depth>300 then
    // Do nothing; it's a diff... Just not perfect and might be really slow to process...
  elseif nadd==1 and ndel==1 then
    (addedTree, deletedTree, before, middle, after, addedBeforeDeleted) := extractSingleAddDiffBeforeAndAfter(res);
    // print("Doing tree diff on selected 1 addition + 1 deletion\n");
    // print("Added tree:"+parseTreeNodeStr(addedTree)+"\n");
    // print("Deleted tree:"+parseTreeNodeStr(deletedTree)+"\n");
    joinTrees := true;
    if compare(addedTree, deletedTree) then
      // This is just a move operation; preserve whitespace
      res := {(Diff.Equal,{deletedTree})};
    elseif isLeaf(deletedTree) and isLeaf(addedTree) then
      res := res;
      joinTrees := false;
    elseif listEmpty(before) and listEmpty(after) then
      if debug then
        print("before and after empty\n");
      end if;
      res := res;
    else
      res := treeDiffWork(getNodes(deletedTree), getNodes(addedTree), depth+1, compare);
    end if;
    if not joinTrees then
      res := res;
      if debug then
        print("not joining trees"+DiffAlgorithm.printDiffTerminalColor(res, parseTreeNodeStr)+"\n");
      end if;
    elseif listEmpty(middle) then
      // We have the add and delete next to each other.
      // This means we can keep the diff as it since nothing moved.
      if debug then
        print("middle empty\n");
      end if;
      res := (Diff.Equal, before) :: listAppend(res, {(Diff.Equal, after)});
    else
      // We have a move with changes. Make the deleted simply be deleted.
      // The added parts become the Equal and Added parts in the diff
      res := list(i for i guard match i case (Diff.Delete,_) then false; else true; end match in res);
      if addedBeforeDeleted then
        res := (Diff.Equal, before) ::
                listAppend(res,
                  (Diff.Equal, middle) ::
                  (Diff.Delete, {deletedTree}) ::
                  {(Diff.Equal, after)});
      else
        res := (Diff.Equal, before) ::
               (Diff.Delete, {deletedTree}) ::
               (Diff.Equal, middle) ::
               listAppend(res,{(Diff.Equal, after)});
      end if;
    end if;
    if debug then
      print(String(depth) + " merged tree size: " + String(stringLength(DiffAlgorithm.printActual(res, SimpleModelicaParser.parseTreeNodeStr))) + "\n");
      print(String(depth) + " before top="+firstTokenDebugStr(before)+"\n");
      print(" before all="+parseTreeStr(before)+"\n");
      print(" middle all="+parseTreeStr(middle)+"\n");
      print(" after all="+parseTreeStr(after)+"\n");
      print("middle top="+firstTokenDebugStr(middle)+"\n");
      print("after top="+firstTokenDebugStr(after)+"\n");
      print("added top="+firstTokenDebugStr(addedTree::{})+"\n");
      print("deleted top="+firstTokenDebugStr(deletedTree::{})+"\n");
    end if;
  elseif nadd>1 and ndel>1 then
    (addedTrees, deletedTrees) := extractAdditionsDeletions(res);
    // TODO: Move this into extractAdditionsDeletions?
    addedTrees := list(t for t guard isLabeledNode(t) in addedTrees);
    deletedTrees := list(t for t guard isLabeledNode(t) in deletedTrees);
    if debug then
      print("number of labeled nodes. add="+String(listLength(addedTrees))+" del="+String(listLength(deletedTrees))+"\n");
    end if;
    // O(D*D)
    for added in addedTrees loop
      for deleted in deletedTrees loop
        if compare(nodeLabel(added),nodeLabel(deleted)) then
          resLocal := treeDiffWork(getNodes(deleted), getNodes(added), depth+1, compare);
          res := replaceLabeledDiff(res, resLocal, nodeLabel(added), compare);
        end if;
      end for;
    end for;
  else
    // print(DiffAlgorithm.printDiffXml(res, parseTreeNodeStr) + "\n");
  end if;
  if debug then
    print("Before filter WS\n");
    print(DiffAlgorithm.printDiffXml(res, parseTreeNodeStr) + "\n");
  end if;
  res := filterDiffWhitespace(res);
  if debug then
    print("After filter WS\n");
    print(DiffAlgorithm.printDiffXml(res, parseTreeNodeStr) + "\n");
  end if;
  if depth==1 then
    // print(DiffAlgorithm.printDiffTerminalColor(res, parseTreeNodeStr) + "\n");
  end if;
end treeDiffWork;

function filterDiffWhitespace
  input list<tuple<Diff,list<ParseTree>>> inDiff;
  output list<tuple<Diff,list<ParseTree>>> diff;
protected
  list<tuple<Diff,list<ParseTree>>> diffLocal=inDiff;
  tuple<Diff,list<ParseTree>> diff1;
  Boolean firstIter, lastTokenNewline, hasAddedWS;
  list<ParseTree> tree, treeLocal, tree1, tree2;
  Integer length, level;
  list<Integer> indentation;
  list<Token> tokens;
  Diff diffEnum;
  String indentationStr;
  Token tok;
algorithm
  diff := {};
  firstIter := true;
  while not listEmpty(diffLocal) loop
    diffLocal := match diffLocal
      // Do not delete whitespace in-between two tokens
      case ((Diff.Delete, tree)::(diffLocal as ((Diff.Equal,_)::_)))
        guard if firstIter then min(parseTreeIsWhitespaceOrParNotComment(t) for t in tree) else false
        algorithm
          diff := (Diff.Equal, tree)::diff;
        then diffLocal;
      case ((diff1 as (Diff.Equal,_))::(Diff.Delete, tree)::(diffLocal as ((Diff.Equal,_)::_)))
        guard min(parseTreeIsWhitespaceOrParNotComment(t) for t in tree)
        algorithm
          diff := (Diff.Equal, tree)::diff1::diff;
        then diffLocal;
      case ((diff1 as (Diff.Equal,_))::(Diff.Delete, tree)::{})
        guard min(parseTreeIsWhitespaceOrParNotComment(t) for t in tree)
        algorithm
          diff := (Diff.Equal, tree)::diff1::diff;
        then diffLocal;
      case ((diff1 as (Diff.Equal,tree1 as (_::_)))::(Diff.Delete, tree)::(diffLocal as ((Diff.Equal,tree2 as (_::_))::_)))
        guard needsWhitespaceBetweenTokens(lastToken(List.last(tree1)), firstTokenInTree(listGet(tree2, 1)))
        algorithm
          diff := (Diff.Equal, {LEAF(makeToken(TokenId.WHITESPACE, " "))})::diff1::diff;
        then diffLocal;
      case ((diff1 as (Diff.Equal,tree1 as (_::_)))::(Diff.Delete, tree)::(diffLocal as ((Diff.Equal,tree2 as (_::_))::_)))
        algorithm
          diff := diff1::diff;
        then (Diff.Delete, tree)::diffLocal;
      // Do not add whitespace for no good reason. Do add whitespace.
      case ((Diff.Add, tree)::(diffLocal as ((Diff.Equal,_)::_)))
        guard if firstIter then min(parseTreeIsWhitespaceOrParNotComment(t) for t in tree) else false
        then diffLocal;
      case ((diff1 as (Diff.Equal,_))::(Diff.Add, tree)::(diffLocal as ((Diff.Equal,_)::_)))
        guard min(parseTreeIsWhitespaceOrParNotComment(t) for t in tree)
        algorithm
          diff := diff1::diff;
        then diffLocal;
      // A normal tree :)
      case diff1::diffLocal
        algorithm
          diff := diff1::diff;
        then diffLocal;
    end match;
    firstIter := false;
  end while;

  diff := listReverseInPlace(diff);
  // Look for indentation levels, try to fix added \n+WS to indent at the same level
  lastTokenNewline := false;
  indentation := {};
  hasAddedWS := false;
  for d in diff loop
    _ := match d
      case (Diff.Add,_)
        algorithm
          for t in tree loop
            _ := match firstNTokensInTree_reverse(t, 2)
              case {LexerModelicaDiff.TOKEN(id=TokenId.WHITESPACE, length=length),LexerModelicaDiff.TOKEN(id=TokenId.NEWLINE)}
                algorithm
                  hasAddedWS := true;
                then ();
              case {LexerModelicaDiff.TOKEN(id=TokenId.WHITESPACE, length=length)} guard lastTokenNewline
                algorithm
                  hasAddedWS := true;
                then ();
              else ();
            end match;
          end for;
        then ();
      case (_,tree)
        algorithm
          for t in tree loop
            _ := match firstNTokensInTree_reverse(t, 2)
              case {LexerModelicaDiff.TOKEN(id=TokenId.WHITESPACE, length=length),LexerModelicaDiff.TOKEN(id=TokenId.NEWLINE)}
                algorithm
                  indentation := length::indentation;
                  lastTokenNewline := false;
                then ();
              case {LexerModelicaDiff.TOKEN(id=TokenId.WHITESPACE, length=length)} guard lastTokenNewline
                algorithm
                  indentation := length::indentation;
                  lastTokenNewline := false;
                then ();
              case {LexerModelicaDiff.TOKEN(id=TokenId.NEWLINE)}
                algorithm
                  lastTokenNewline := true;
                then ();
              case tokens
                algorithm
                  lastTokenNewline := false;
                then ();
            end match;
          end for;
        then ();
    end match;
  end for;
  if listEmpty(indentation) or (not hasAddedWS) then
    if debug then
      print("Skipping indentation as we could not auto-detect suitable indentation levels\n");
    end if;
    return;
  end if;
  // We have a known indentation level and added \n+WS; try to fix it
  level := min(l for l in indentation);
  indentationStr := StringUtil.repeat(" ", level);
  diffLocal := {};
  for d in diff loop
    _ := match d
      case (Diff.Delete,tree)
        algorithm
          diffLocal := d::diffLocal;
        then ();
      case (diffEnum, tree)
        algorithm
          treeLocal := {};
          hasAddedWS := false;
          for t in tree loop
            _ := match (diffEnum, firstNTokensInTree_reverse(t, 2))
              case (Diff.Equal, _)
                algorithm
                then ();
              case (_, {LexerModelicaDiff.TOKEN(id=TokenId.WHITESPACE, length=length),tok as LexerModelicaDiff.TOKEN(id=TokenId.NEWLINE)})
                algorithm
                  treeLocal := replaceFirstTokensInTree(t, {tok,makeToken(TokenId.WHITESPACE, indentationStr)})::treeLocal;
                  hasAddedWS := true;
                then ();
              case (_, {LexerModelicaDiff.TOKEN(id=TokenId.WHITESPACE, length=length)}) guard lastTokenNewline
                algorithm
                  treeLocal := replaceFirstTokensInTree(t, {makeToken(TokenId.WHITESPACE, indentationStr)})::treeLocal;
                  hasAddedWS := true;
                then ();
              else
                algorithm
                  treeLocal := t::treeLocal;
                then ();
            end match;
            lastTokenNewline := match lastToken(t) case LexerModelicaDiff.TOKEN(id=TokenId.NEWLINE) then true; else false; end match;
          end for;
          diffLocal := if hasAddedWS then ((diffEnum, listReverse(treeLocal))::diffLocal) else (d::diffLocal);
        then ();
    end match;
  end for;
  diff := listReverseInPlace(diffLocal);
end filterDiffWhitespace;

function makeToken
  input TokenId id;
  input String str;
  output Token token;
algorithm
  token := LexerModelicaDiff.TOKEN("<dummy>", id, str, 1, stringLength(str), 0, 0, 0, 0);
  annotation(__OpenModelica_EarlyInline=true);
end makeToken;

function replaceLabeledDiff
  input list<tuple<Diff,list<ParseTree>>> inDiff, diffedNodes;
  input ParseTree labelOfDiffedNodes;
  input CmpParseTreeFunc compare;
  output list<tuple<Diff,list<ParseTree>>> res={};
protected
  list<tuple<Diff,list<ParseTree>>> filtered;
  list<ParseTree> lst, acc;
algorithm
  for diff in inDiff loop
    res := match diff
      case (Diff.Equal, _) then diff::res;
      case (Diff.Add, lst) guard not max(compare(nodeLabel(t), labelOfDiffedNodes) for t in lst) then diff::res;
      case (Diff.Delete, lst) guard not max(compare(nodeLabel(t), labelOfDiffedNodes) for t in lst) then diff::res;
      case (Diff.Delete, lst) then (Diff.Delete, list(t for t guard not compare(nodeLabel(t), labelOfDiffedNodes) in lst))::res; // TODO: Handle the deletion better...
      case (Diff.Add, lst)
        algorithm
          acc := {};
          for t in lst loop
            // Assuming adjacent to the delete node
            if compare(nodeLabel(t), labelOfDiffedNodes) then
              if not listEmpty(acc) then
                res := (Diff.Add, listReverse(acc))::res;
                acc := {};
              end if;
              // filtered := listReverse(diffedNodes);
              filtered := listReverse(i for i guard match i case (Diff.Delete,_) then false; else true; end match in diffedNodes);
              res := listAppend(filtered, res);
            end if;
          end for;
          if not listEmpty(acc) then
            res := (Diff.Add, listReverse(acc))::res;
          end if;
        then res;
    end match;
  end for;
  res := listReverse(res);
end replaceLabeledDiff;

function isLabeledNode
  input ParseTree tree;
  output Boolean b;
algorithm
  b := match tree
    case NODE(label=EMPTY()) then false;
    case NODE() then true;
    else false;
  end match;
end isLabeledNode;

function nodeLabel
  input ParseTree tree;
  output ParseTree label;
algorithm
  label := match tree
    case NODE() then tree.label;
    else EMPTY();
  end match;
end nodeLabel;

function parseTreeEq
  input ParseTree t1, t2;
  input array<Token> diffSubtreeWorkArray1, diffSubtreeWorkArray2;
  output Boolean b;
protected
  Integer len1, len2, commentLen1, commentLen2;
algorithm
  // try
    (len1,commentLen1) := findTokens(t1, diffSubtreeWorkArray1);
    (len2,commentLen2) := findTokens(t2, diffSubtreeWorkArray2);
  /*else
    print("parseTreeEq failed: t1=" + parseTreeStr({t1}) + "\n");
    print("parseTreeEq failed: t2=" + parseTreeStr({t2}) + "\n");
  end try;*/
  b := false;
  if len1 <> len2 or commentLen1 <> commentLen2 then
    return;
  end if;
  for i in 1:len1 loop
    if not modelicaDiffTokenEq(diffSubtreeWorkArray1[i], diffSubtreeWorkArray2[i]) then
      return;
    end if;
  end for;
  for i in 1:commentLen1 loop
    if not modelicaDiffTokenEq(diffSubtreeWorkArray1[arrayLength(diffSubtreeWorkArray1)-(i-1)], diffSubtreeWorkArray2[arrayLength(diffSubtreeWorkArray2)-(i-1)]) then
      return;
    end if;
  end for;
  b := true;
end parseTreeEq;

function findTokens
  input ParseTree t;
  input array<Token> work;
  input Integer inCount=0;
  input Integer inCommentCount=0;
  output Integer count=inCount;
  output Integer commentCount=inCommentCount;
algorithm
  if parseTreeIsComment(t) then
    arrayUpdate(work, arrayLength(work)-commentCount, firstTokenInTree(t));
    commentCount := commentCount + 1;
    return;
  elseif parseTreeIsWhitespaceOrPar(t) then
    return;
  end if;
  _ := match t
    case EMPTY() then ();
    case LEAF()
      algorithm
        count := count+1;
        arrayUpdate(work, count, t.token);
      then ();
    case NODE()
      algorithm
        for n in t.nodes loop
          (count, commentCount) := findTokens(n, work, count, commentCount);
        end for;
      then ();
  end match;
end findTokens;

function replaceFirstTokensInTree
  input ParseTree t;
  input list<Token> tokens;
  output ParseTree tree;
algorithm
  (tree, {}) := replaceFirstTokensInTreeWork(t, tokens);
end replaceFirstTokensInTree;

function replaceFirstTokensInTreeWork
  input ParseTree t;
  input list<Token> inTokens;
  output ParseTree tree=t;
  output list<Token> tokens=inTokens;
protected
  list<ParseTree> work, acc;
  ParseTree n;
  Token tok;
algorithm
  (tree, tokens) := match (tree, tokens)
    case (tree, {}) then (tree, tokens);
    case (EMPTY(), _) then (tree, tokens);
    case (LEAF(), tok::tokens) then (LEAF(tok), tokens);
    case (NODE(), tokens)
      algorithm
        work := tree.nodes;
        acc := {};
        while not listEmpty(work) loop
          n::work := work;
          (n, tokens) := replaceFirstTokensInTreeWork(n, tokens);
          if listEmpty(tokens) then
            tree.nodes := List.append_reverse(acc, n::work);
            return;
          else
            acc := n::acc;
          end if;
        end while;
        tree.nodes := listReverse(acc);
      then (tree, tokens);
  end match;
end replaceFirstTokensInTreeWork;

function firstNTokensInTree_reverse
  input ParseTree t;
  input Integer n;
  input list<Token> acc={};
  output list<Token> tokens=acc;
algorithm
  if listLength(tokens)>1 then
    return;
  end if;
  tokens := match t
    case EMPTY() then tokens;
    case LEAF() then t.token::tokens;
    case NODE()
      algorithm
        for node in t.nodes loop
          tokens := firstNTokensInTree_reverse(node, n, tokens);
          if listLength(tokens)>1 then
            return;
          end if;
        end for;
      then acc;
  end match;
end firstNTokensInTree_reverse;

function firstTokenInTree
  input ParseTree t;
  output Token token;
algorithm
  token := match t
    case EMPTY() then fail();
    case LEAF() then t.token;
    case NODE() then firstTokenInTree(listGet(t.nodes, 1));
  end match;
end firstTokenInTree;

function lastToken
  input ParseTree t;
  output Token token;
algorithm
  token := match t
    case EMPTY() then fail();
    case LEAF() then t.token;
    case NODE() then lastToken(List.last(t.nodes));
  end match;
end lastToken;

function fixMoveOperations "Move operations are very common, but result
  in delete+add operations in the diff algorithm. Here we fix things so
  the addition is using the exact same tokens as the original.

  Time cost O(N*D). The number of diffs is typically low since we compare
  parse trees"
  input list<tuple<Diff,list<ParseTree>>> inDiff;
  input CmpParseTreeFunc compare;
  output list<tuple<Diff,list<ParseTree>>> diff = {};
protected
  list<ParseTree> lst, deleted={}, lst2;
  Boolean changeFound=false;
  tuple<Diff, list<ParseTree>> d1;
algorithm
  for d in inDiff loop
    _ := match d
      case (Diff.Delete, lst)
        algorithm
          deleted := listAppend(lst, deleted);
        then ();
      else ();
    end match;
  end for;
  if listEmpty(deleted) then
    diff := inDiff;
    return;
  end if;
  for d in inDiff loop
    d1 := match d
      case (Diff.Add, lst)
        algorithm
          d1 := d;
          for l1 in lst loop
            if List.isMemberOnTrue(l1, deleted, compare) then
              changeFound := true;
              lst2 := {};
              for l2 in lst loop
                try
                  lst2 := List.getMemberOnTrue(l1, deleted, compare)::lst2;
                else
                  lst2 := l2::lst2;
                end try;
              end for;
              d1 := (Diff.Add, listReverseInPlace(lst2));
              break;
            end if;
          end for;
        then d1;
      else d;
    end match;
    diff := d1::diff;
  end for;
  diff := if changeFound then listReverseInPlace(diff) else inDiff;
end fixMoveOperations;

function makeNode
  input list<ParseTree> nodes;
  input ParseTree label = EMPTY();
  output ParseTree node;
algorithm
  node := match nodes
    case {}
      algorithm
        error({}, nodes, {});
      then fail();
    case {node} guard match label case EMPTY() then true; else false; end match then node;
    else NODE(label, nodes);
  end match;
end makeNode;

function makeNodePrependTree
  input list<ParseTree> nodes;
  input list<ParseTree> tree;
  input ParseTree label = EMPTY();
  output list<ParseTree> outTree;
algorithm
  outTree := if not listEmpty(nodes) then makeNode(nodes, label)::tree else tree;
end makeNodePrependTree;

function isLeaf
  input ParseTree t;
  output Boolean b;
algorithm
  b := match t
    case LEAF() then true;
    else false;
  end match;
end isLeaf;

function firstToken
  input list<ParseTree> t;
  output Token token;
algorithm
  token := match t
    local
      list<ParseTree> nodes;
    case NODE(nodes=nodes)::_ then firstToken(nodes);
    case LEAF(token)::_ then token;
    else LexerModelicaDiff.noToken;
  end match;
end firstToken;

function firstTokenDebugStr
  input list<ParseTree> t;
  output String str;
protected
  list<Token> l;
algorithm
  l := firstToken(t)::{};
  str := Error.infoStr(topTokenSourceInfo(l))+" "+topTokenStr(l);
end firstTokenDebugStr;

function getNodes
  input ParseTree t;
  output list<ParseTree> nodes;
algorithm
  nodes := match t
    case NODE() then t.nodes;
    else {t};
  end match;
end getNodes;

function extractSingleAddDiffBeforeAndAfter "Ignores whitespace"
  input list<tuple<Diff,list<ParseTree>>> diffs;
  output ParseTree addedTree, deletedTree;
  output list<ParseTree> before, middle, after;
  output Boolean addedBeforeDeleted;
protected
  Boolean foundAdded=false;
  Boolean foundDeleted=false;
  list<list<ParseTree>> acc={};
  list<ParseTree> trees, lst;
  Diff d;
algorithm
  for diff in diffs loop
    _ := match diff
      case (Diff.Add, lst)
        algorithm
          for tree in lst loop
            if parseTreeIsWhitespace(tree) then
              acc := acc;
            elseif parseTreeIsWhitespaceOrPar(tree) then
              acc := {tree}::acc;
            else
              if foundAdded then
                Error.addInternalError("Found multiple Add subtrees", sourceInfo());
                fail();
              end if;
              addedTree := tree;
              foundAdded := true;
              if foundDeleted then
                middle := List.flatten(listReverse(acc));
              else
                addedBeforeDeleted := true;
                before := List.flatten(listReverse(acc));
              end if;
              acc := {};
            end if;
          end for;
        then ();
      case (Diff.Delete, lst)
        algorithm
          for tree in lst loop
            if parseTreeIsWhitespaceOrPar(tree) then
              acc := {tree}::acc;
            else
              if foundDeleted then
                Error.addInternalError("Found multiple Delete subtrees", sourceInfo());
                fail();
              end if;
              deletedTree := tree;
              foundDeleted := true;
              if foundAdded then
                middle := List.flatten(listReverse(acc));
              else
                addedBeforeDeleted := false;
                before := List.flatten(listReverse(acc));
              end if;
              acc := {};
            end if;
          end for;
        then ();
      case (Diff.Equal, trees)
        algorithm
          acc := trees::acc;
        then ();
      case (d, _)
        algorithm
          Error.addInternalError("Found "+String(d)+" subtrees with multiple or zero entries", sourceInfo());
        then fail();
    end match;
  end for;
  true := foundAdded;
  true := foundDeleted;
  after := List.flatten(listReverse(acc));
end extractSingleAddDiffBeforeAndAfter;

function extractAdditionsDeletions
  input list<tuple<Diff,list<ParseTree>>> diffs;
  output list<ParseTree> addedTrees, deletedTrees;
protected
  list<list<ParseTree>> addedTreesAcc={}, deletedTreesAcc={};
  list<ParseTree> lst;
algorithm
  for diff in diffs loop
    _ := match diff
      case (Diff.Add, lst)
        algorithm
          addedTreesAcc := lst::addedTreesAcc;
        then ();
      case (Diff.Delete, lst)
        algorithm
          deletedTreesAcc := lst::deletedTreesAcc;
        then ();
      else ();
    end match;
  end for;
  addedTrees := List.flatten(listReverse(addedTreesAcc));
  deletedTrees := List.flatten(listReverse(deletedTreesAcc));
end extractAdditionsDeletions;

function countDiffAddDelete
  input list<tuple<Diff,list<ParseTree>>> diffs;
  output Integer nadd=0;
  output Integer ndel=0;
protected
  Diff d;
  list<ParseTree> l;
algorithm
  for diff in diffs loop
    (d,l) := diff;
    if d == Diff.Add then
      nadd := nadd+sum(if parseTreeIsWhitespaceOrPar(t) then 0 else 1 for t in l);
    elseif d == Diff.Delete then
      ndel := ndel+sum(if parseTreeIsWhitespaceOrPar(t) then 0 else 1 for t in l);
    end if;
  end for;
end countDiffAddDelete;

constant list<TokenId> whiteSpaceTokenIds = {
    TokenId.LINE_COMMENT,
    TokenId.BLOCK_COMMENT,
    TokenId.NEWLINE,
    TokenId.WHITESPACE
};

constant list<TokenId> whiteSpaceTokenIdsNotComment = {
    TokenId.NEWLINE,
    TokenId.WHITESPACE
};

constant list<TokenId> tokenIdsComment = {
    TokenId.LINE_COMMENT,
    TokenId.BLOCK_COMMENT
};

function dummyParseTreeIsWhitespaceFalse
  // The diff-algorithm will strip leading whitespace, but these are
  // sort of significant...
  input ParseTree t1;
  output Boolean b=false;
end dummyParseTreeIsWhitespaceFalse;

function parseTreeIsWhitespace
  input ParseTree t1;
  output Boolean b;
protected
  TokenId id;
algorithm
  b := match t1
    case LEAF() then listMember(t1.token.id, whiteSpaceTokenIds);
    else false;
  end match;
end parseTreeIsWhitespace;

function parseTreeIsWhitespaceOrPar
  input ParseTree t1;
  output Boolean b;
protected
  TokenId id;
algorithm
  b := match t1
    case LEAF() then listMember(t1.token.id, TokenId.LPAR::TokenId.RPAR::whiteSpaceTokenIds);
    else false;
  end match;
end parseTreeIsWhitespaceOrPar;

function parseTreeIsWhitespaceOrParNotComment
  input ParseTree t1;
  output Boolean b;
protected
  TokenId id;
algorithm
  b := match t1
    case LEAF() then listMember(t1.token.id, TokenId.LPAR::TokenId.RPAR::whiteSpaceTokenIdsNotComment);
    else false;
  end match;
end parseTreeIsWhitespaceOrParNotComment;

function parseTreeIsComment
  input ParseTree t1;
  output Boolean b;
protected
  TokenId id;
algorithm
  b := match t1
    case LEAF() then listMember(t1.token.id, tokenIdsComment);
    else false;
  end match;
end parseTreeIsComment;

function eatWhitespace
  extends partialParser;
protected
  TokenId id;
  Token t;
algorithm
  tree := inTree;
  while match tokens case LexerModelicaDiff.TOKEN(id=id)::_ then listMember(id, {TokenId.LINE_COMMENT, TokenId.BLOCK_COMMENT, TokenId.NEWLINE, TokenId.WHITESPACE}); else false; end match loop
    t::tokens := tokens;
    tree := LEAF(t)::tree;
  end while;
  outTree := tree;
end eatWhitespace;

function scanOpt
  extends partialParser;
  input TokenId id;
  output Boolean found;
protected
  TokenId id2;
  Token t;
  list<Token> tokens2;
algorithm
  (tokens, tree) := eatWhitespace(tokens, inTree);
  (tokens, tree, found) := match tokens
    case (t as LexerModelicaDiff.TOKEN(id=id2))::tokens2 guard id==id2 then (tokens2, LEAF(t)::tree, true);
    else (tokens, tree, false);
  end match;
  if not found then
    // We want whitespace to be part of the next node; not added as a
    // separate node that gets eaten in the previous one.
    // This is bad for performance resons (we eat the same whitespace multiple
    // times. But we do not want to backpatch and guess indentation level.
    outTree := inTree;
    tokens := inTokens;
  else
    outTree := tree;
  end if;
end scanOpt;

function scan
  extends partialParser;
  input TokenId id;
protected
  Boolean found;
  TokenId id2;
algorithm
  tree := inTree;
  (tokens, tree, found) := scanOpt(tokens, tree, id);
  if not found then
    error(tokens, tree, {id});
  end if;
  outTree := tree;
end scan;

function scanOneOf
  extends partialParser;
  input list<TokenId> ids;
protected
  Boolean found;
  TokenId id2;
algorithm
  tree := inTree;
  (tokens, tree, found) := LA1(tokens, tree, ids, consume=true);
  if not found then
    error(tokens, tree, ids);
  end if;
  outTree := tree;
end scanOneOf;

function error
  input list<Token> tokens;
  input list<ParseTree> tree;
  input list<TokenId> expected;
protected
  Integer i;
  String s;
  list<String> strs, res;
  SourceInfo info;
algorithm
  info := topTokenSourceInfo(tokens);
  res := ("Failed to scan top of input: " + topTokenStr(tokens) + "\n  Expected one of: " + (if listEmpty(expected) then "<EOF>" else stringDelimitList(list(tokenIdStr(id) for id in expected), ", ")) + "\n")::{};
  res := ("  Current parse tree is:\n" + parseTreeStr(listReverse(tree)) + "\n  The parser stack is:\n")::res;
  StackOverflow.setStacktraceMessages(0, 100);
  for s in StackOverflow.readableStacktraceMessages() loop
    (i, strs) := System.regex(s, "SimpleModelicaParser[^A-Za-z]([A-Za-z_0-9_]*)", 2, true, false);
    _ := match (i, strs)
      case (2, {_,s}) guard s<>"error"
        algorithm
          res := "\n"::s::res;
        then ();
      else ();
    end match;
  end for;
  Error.addInternalError(stringAppendList(listReverse(res)), info);
  fail();
end error;

function tokenIdStr
  input TokenId id;
  output String str = String(id);
end tokenIdStr;

function peek
  extends partialParser;
  output TokenId id;
algorithm
  tree := inTree;
  (tokens, tree) := eatWhitespace(tokens, tree);
  id := match tokens
    case LexerModelicaDiff.TOKEN(id=id)::_ then id;
    else TokenId._NO_TOKEN;
  end match;
  outTree := tree;
end peek;

function consume
  extends partialParser;
protected
  Token t;
algorithm
  t::tokens := tokens;
  outTree := LEAF(t)::inTree;
end consume;

function LA1 "Do look-ahead 1 token and see if the token is one of the given ones."
  extends partialParser;
  input list<TokenId> ids;
  input Boolean consume=false;
  output Boolean found;
protected
  TokenId id;
algorithm
  tree := inTree;
  (tokens, tree) := eatWhitespace(tokens, tree);
  found := match tokens
    case LexerModelicaDiff.TOKEN(id=id)::_ then listMember(id, ids);
    else false;
  end match;
  if found and consume then
    (tokens,tree) := SimpleModelicaParser.consume(tokens, tree);
  end if;
  if not found then
    outTree := inTree;
    tokens := inTokens;
  else
    outTree := tree;
  end if;
end LA1;

function LAk "Do look-ahead k tokens and see if the tokens match one of the given ones."
  extends partialParser;
  input list<list<TokenId>> idsLst "k sets of tokens to check";
  output Boolean found;
protected
  TokenId id;
  list<Token> tmp;
algorithm
  tree := inTree;
  (tokens, tree) := eatWhitespace(tokens, tree);
  outTree := tree;
  tmp := tokens;
  for ids in idsLst loop
    found := match tmp
      case LexerModelicaDiff.TOKEN(id=id)::tmp then listMember(id, ids);
      else false;
    end match;
    if not found then
      return;
    end if;
    (tmp) := eatWhitespace(tmp, {});
  end for;
end LAk;

function parseTreeStrWork
  input ParseTree tree;
protected
  Integer i;
algorithm
  _ := match tree
    // TODO: Normalize line-endings? We can output mixed CRLF/LF now...
    case LEAF() algorithm Print.printBuf(tokenContent(tree.token)); then ();
    case EMPTY() algorithm Print.printBuf("<EMPTY>"); then ();
    case NODE()
      algorithm
        for n in tree.nodes loop
          parseTreeStrWork(n);
        end for;
      then ();
  end match;
end parseTreeStrWork;

function topTokenStr
  input list<Token> tokens;
  output String str;
protected
  TokenId id;
  Token t;
algorithm
  str := (match tokens case (t as LexerModelicaDiff.TOKEN(id=id))::_ then String(id)+" ("+tokenContent(t)+")"; else "EOF"; end match);
end topTokenStr;

function topTokenSourceInfo
  input list<Token> tokens;
  output SourceInfo info;
protected
  Token t;
algorithm
  info := (match tokens case t::_
    then LexerModelicaDiff.tokenSourceInfo(t);
    else SOURCEINFO("<SimpleModelicaParser>", false, 0, 0, 0, 0, 0.0); end match);
end topTokenSourceInfo;

function needsWhitespaceBetweenTokens
  input Token first, last;
  output Boolean b;
protected
  constant list<TokenId> notident = {
    TokenId.ASSIGN,
    TokenId.BLOCK_COMMENT,
    TokenId.COLON,
    TokenId.COLONCOLON,
    TokenId.COMMA,
    TokenId.DOT,
    TokenId.EQEQ,
    TokenId.EQUALS,
    TokenId.GREATER,
    TokenId.GREATEREQ,
    TokenId.LBRACE,
    TokenId.LBRACK,
    TokenId.LESS,
    TokenId.LESSEQ,
    TokenId.LESSGT,
    TokenId.LINE_COMMENT,
    TokenId.LPAR,
    TokenId.MINUS,
    TokenId.MINUS_EW,
    TokenId.NEWLINE,
    TokenId.OPERATOR,
    TokenId.PLUS,
    TokenId.PLUS_EW,
    TokenId.POWER,
    TokenId.POWER_EW,
    TokenId.RBRACE,
    TokenId.RBRACK,
    TokenId.RPAR,
    TokenId.SEMICOLON,
    TokenId.SLASH,
    TokenId.SLASH_EW,
    TokenId.STAR,
    TokenId.STAR_EW,
    TokenId.STRING,
    TokenId.UNSIGNED_INTEGER,
    TokenId.UNSIGNED_REAL,
    TokenId.WHITESPACE
  };
  Boolean b1, b2;
algorithm
  if listMember(tokenId(first), notident) or listMember(tokenId(last), notident) then
    b := false;
    return;
  end if;
  // Assuming the grammar is nice to us...
  b := true;
end needsWhitespaceBetweenTokens;

function tokenId
  input Token t;
  output TokenId id;
algorithm
  LexerModelicaDiff.TOKEN(id=id) := t;
end tokenId;

package First "First token possible for a given non-terminal in the Modelica 3 grammar"
  constant list<TokenId> class_prefixes = {
    TokenId.PARTIAL,
    TokenId.CLASS,
    TokenId.MODEL,
    TokenId.OPERATOR,
    TokenId.RECORD,
    TokenId.BLOCK,
    TokenId.EXPANDABLE,
    TokenId.CONNECTOR,
    TokenId.TYPE,
    TokenId.PACKAGE,
    TokenId.PURE,
    TokenId.IMPURE,
    TokenId.FUNCTION
  };
  constant list<TokenId> class_definition =
    TokenId.FINAL ::
    TokenId.ENCAPSULATED ::
    class_prefixes
  ;
  constant list<TokenId> class_modification = {
    TokenId.LPAR
  };
  constant list<TokenId> type_prefix = {
    TokenId.FLOW,
    TokenId.STREAM,
    TokenId.DISCRETE,
    TokenId.PARAMETER,
    TokenId.CONSTANT,
    TokenId.INPUT,
    TokenId.OUTPUT
  };
  constant list<TokenId> class_modification = {
    TokenId.LPAR
  };
  constant list<TokenId> _annotation = {
    TokenId.ANNOTATION
  };
  constant list<TokenId> element_redeclaration = {
    TokenId.REDECLARE
  };
  constant list<TokenId> name = {
    TokenId.DOT,
    TokenId.IDENT
  };
  constant list<TokenId> element_modification_or_replaceable =
    TokenId.EACH::
    TokenId.FINAL::
    TokenId.REPLACEABLE::
    name
  ;
  constant list<TokenId> argument = listAppend(
    element_modification_or_replaceable,
    element_redeclaration
  );
  constant list<TokenId> modification = {
    TokenId.LPAR,
    TokenId.EQUALS,
    TokenId.ASSIGN
  };
  constant list<TokenId> component_clause = listAppend(type_prefix,name);
  constant list<TokenId> element = listAppend(component_clause, listAppend(class_definition, {
    TokenId.IMPORT,
    TokenId.EXTENDS,
    TokenId.REDECLARE,
    TokenId.FINAL,
    TokenId.INNER,
    TokenId.OUTER,
    TokenId.REPLACEABLE
  }));
  constant list<TokenId> statement = {
    TokenId.DOT,
    TokenId.IDENT,
    TokenId.LPAR,
    TokenId.BREAK,
    TokenId.RETURN,
    TokenId.IF,
    TokenId.FOR,
    TokenId.WHILE,
    TokenId.WHEN
  };
  constant list<TokenId> component_reference = {
    TokenId.DOT,
    TokenId.IDENT
  };
/*  constant list<TokenId> function_arguments =
    TokenId.FUNCTION ::
    TokenId.IDENT ::
    expression
  ; */
end First;

package Follow
  constant list<TokenId> statement_equation = {
    TokenId.INITIAL, // Only potential conflict
    TokenId.EQUATION,
    TokenId.ALGORITHM,
    TokenId.PUBLIC,
    TokenId.PROTECTED,
    TokenId.EXTERNAL,
    TokenId.ANNOTATION,
    TokenId.ELSE,
    TokenId.ELSEIF,
    TokenId.END,
    TokenId.ELSEWHEN
  };
end Follow;

constant Boolean debug = false;

annotation(__OpenModelica_Interface="backend");
end SimpleModelicaParser;
