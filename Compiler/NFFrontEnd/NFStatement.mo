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

encapsulated uniontype NFStatement
  import Absyn;
  import Type = NFType;
  import Expression = NFExpression;
  import NFInstNode.InstNode;

protected
  import Statement = NFStatement;

public
  record ASSIGNMENT
    Expression lhs "The asignee";
    Expression rhs "The expression";
    SourceInfo info;
  end ASSIGNMENT;

  record FUNCTION_ARRAY_INIT "Used to mark in which order local array variables in functions should be initialized"
    String name;
    Type ty;
    SourceInfo info;
  end FUNCTION_ARRAY_INIT;

  record FOR
    InstNode iterator;
    list<Statement> body "The body of the for loop.";
    SourceInfo info;
  end FOR;

  record IF
    list<tuple<Expression, list<Statement>>> branches
      "List of branches, where each branch is a tuple of a condition and a body.";
    SourceInfo info;
  end IF;

  record WHEN
    list<tuple<Expression, list<Statement>>> branches
      "List of branches, where each branch is a tuple of a condition and a body.";
    SourceInfo info;
  end WHEN;

  record ASSERT
    Expression condition "The assert condition.";
    Expression message "The message to display if the assert fails.";
    Expression level;
    SourceInfo info;
  end ASSERT;

  record TERMINATE
    Expression message "The message to display if the terminate triggers.";
    SourceInfo info;
  end TERMINATE;

  record NORETCALL
    Expression exp;
    SourceInfo info;
  end NORETCALL;

  record WHILE
    Expression condition;
    list<Statement> body;
    SourceInfo info;
  end WHILE;

  record RETURN
    SourceInfo info;
  end RETURN;

  record BREAK
    SourceInfo info;
  end BREAK;

  record FAILURE
    list<Statement> body;
    SourceInfo info;
  end FAILURE;

  function info
    input Statement stmt;
    output SourceInfo info;
  algorithm
    info := match stmt
      case ASSIGNMENT() then stmt.info;
      case FUNCTION_ARRAY_INIT() then stmt.info;
      case FOR() then stmt.info;
      case IF() then stmt.info;
      case WHEN() then stmt.info;
      case ASSERT() then stmt.info;
      case TERMINATE() then stmt.info;
      case NORETCALL() then stmt.info;
      case WHILE() then stmt.info;
      case RETURN() then stmt.info;
      case BREAK() then stmt.info;
      case FAILURE() then stmt.info;
    end match;
  end info;

  function mapExpList
    input output list<Statement> stmtl;
    input MapFunc func;

    partial function MapFunc
      input output Expression exp;
    end MapFunc;
  algorithm
    stmtl := list(mapExp(s, func) for s in stmtl);
  end mapExpList;

  function mapExp
    input output Statement stmt;
    input MapFunc func;

    partial function MapFunc
      input output Expression exp;
    end MapFunc;
  algorithm
    stmt := match stmt
      local
        Expression e1, e2, e3;

      case ASSIGNMENT()
        algorithm
          e1 := func(stmt.lhs);
          e2 := func(stmt.rhs);
        then
          if referenceEq(e1, stmt.lhs) and referenceEq(e2, stmt.rhs) then
            stmt else ASSIGNMENT(e1, e2, stmt.info);

      case FOR()
        algorithm
          stmt.body := mapExpList(stmt.body, func);
        then
          stmt;

      case IF()
        algorithm
          stmt.branches := list(
            (func(Util.tuple21(b)), mapExpList(Util.tuple22(b), func)) for b in stmt.branches);
        then
          stmt;

      case WHEN()
        algorithm
          stmt.branches := list(
            (func(Util.tuple21(b)), mapExpList(Util.tuple22(b), func)) for b in stmt.branches);
        then
          stmt;

      case ASSERT()
        algorithm
          e1 := func(stmt.condition);
          e2 := func(stmt.message);
          e3 := func(stmt.level);
        then
          if referenceEq(e1, stmt.condition) and referenceEq(e2, stmt.message) and
            referenceEq(e3, stmt.level) then stmt else ASSERT(e1, e2, e3, stmt.info);

      case TERMINATE()
        algorithm
          e1 := func(stmt.message);
        then
          if referenceEq(e1, stmt.message) then stmt else TERMINATE(e1, stmt.info);

      case NORETCALL()
        algorithm
          e1 := func(stmt.exp);
        then
          if referenceEq(e1, stmt.exp) then stmt else NORETCALL(e1, stmt.info);

      case WHILE()
        then WHILE(func(stmt.condition), mapExpList(stmt.body, func), stmt.info);

      else stmt;
    end match;
  end mapExp;

  function foldExpList<ArgT>
    input list<Statement> stmt;
    input FoldFunc func;
    input output ArgT arg;

    partial function FoldFunc
      input Expression exp;
      input output ArgT arg;
    end FoldFunc;
  algorithm
    for s in stmt loop
      arg := foldExp(s, func, arg);
    end for;
  end foldExpList;

  function foldExp<ArgT>
    input Statement stmt;
    input FoldFunc func;
    input output ArgT arg;

    partial function FoldFunc
      input Expression exp;
      input output ArgT arg;
    end FoldFunc;
  algorithm
    () := match stmt
      case Statement.ASSIGNMENT()
        algorithm
          arg := func(stmt.lhs, arg);
          arg := func(stmt.rhs, arg);
        then
          ();

      case Statement.FOR()
        algorithm
          arg := foldExpList(stmt.body, func, arg);
        then
          ();

      case Statement.IF()
        algorithm
          for b in stmt.branches loop
            arg := func(Util.tuple21(b), arg);
            arg := foldExpList(Util.tuple22(b), func, arg);
          end for;
        then
          ();

      case Statement.WHEN()
        algorithm
          for b in stmt.branches loop
            arg := func(Util.tuple21(b), arg);
            arg := foldExpList(Util.tuple22(b), func, arg);
          end for;
        then
          ();

      case Statement.ASSERT()
        algorithm
          arg := func(stmt.condition, arg);
          arg := func(stmt.message, arg);
          arg := func(stmt.level, arg);
        then
          ();

      case Statement.TERMINATE()
        algorithm
          arg := func(stmt.message, arg);
        then
          ();

      case Statement.NORETCALL()
        algorithm
          arg := func(stmt.exp, arg);
        then
          ();

      case Statement.WHILE()
        algorithm
          arg := func(stmt.condition, arg);
          arg := foldExpList(stmt.body, func, arg);
        then
          ();

      else ();
    end match;
  end foldExp;

annotation(__OpenModelica_Interface="frontend");
end NFStatement;
