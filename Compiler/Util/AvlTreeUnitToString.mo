encapsulated package AvlTreeUnitToString
  import BaseAvlTree;
  import Unit;
  extends BaseAvlTree;

  redeclare type Key = Unit.Unit;
  redeclare type Value = String;

  redeclare function extends keyStr
  algorithm
    outString := Unit.unit2string(inKey);
  end keyStr;

  redeclare function extends valueStr
  algorithm
    outString := inValue;
  end valueStr;

  redeclare function extends keyCompare
  algorithm
    outResult := stringCompare(Unit.unit2string(inKey1), Unit.unit2string(inKey2));
  end keyCompare;
annotation(__OpenModelica_Interface="backend");
end AvlTreeUnitToString;
