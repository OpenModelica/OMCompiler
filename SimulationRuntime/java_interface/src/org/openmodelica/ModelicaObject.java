package org.openmodelica;

public interface ModelicaObject {
  /*
   * Modelica Array {1,2,3,4,5,6}
   * MetaModelica List {1,2,3,4,5,6}
   * OMC accepts same syntax and auto-converts them. So we can use the same structure if we want...
   */
  public void setObject(ModelicaObject o);
  /**
   * Same as toString(), but more efficient
   */
  public void printToBuffer(StringBuffer buffer);
}
