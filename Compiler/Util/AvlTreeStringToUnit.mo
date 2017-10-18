encapsulated package AvlTreeStringToUnit
  import BaseAvlTree;
  import Unit;
  extends BaseAvlTree;

  redeclare type Key = String;
  redeclare type Value = Unit.Unit;

  redeclare function extends keyStr
  algorithm
    outString := inKey;
  end keyStr;

  redeclare function extends valueStr
  algorithm
    outString := Unit.unit2string(inValue);
  end valueStr;

  redeclare function extends keyCompare
  algorithm
    outResult := stringCompare(inKey1, inKey2);
  end keyCompare;
annotation(__OpenModelica_Interface="backend");
end AvlTreeStringToUnit;
