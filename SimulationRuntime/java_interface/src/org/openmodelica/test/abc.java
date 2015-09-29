package org.openmodelica.test;

import java.io.IOException;
import java.io.Reader;
import java.util.Map;

import org.openmodelica.ModelicaInteger;
import org.openmodelica.ModelicaObject;
import org.openmodelica.ModelicaReal;
import org.openmodelica.ModelicaRecord;
import org.openmodelica.ModelicaRecordException;
import org.openmodelica.SimpleTypeSpec;
import org.openmodelica.corba.parser.ParseException;

/* The class needs to be public and not a nested class because
 * it has be accessed by the proxy through reflection. If it's part of
 * another class the constructor has a different signature (Java sends the parent
 * class as an argument to nested classes). */

@SuppressWarnings("unchecked")
public class abc extends ModelicaRecord implements ABC_UT {
  private static final long serialVersionUID = -2570450403100665253L;
  private static org.openmodelica.TypeSpec<? extends ModelicaObject>[] fieldTypeSpecs;

  static {
    fieldTypeSpecs = new org.openmodelica.TypeSpec[] {
      new SimpleTypeSpec(ModelicaInteger.class),
      new SimpleTypeSpec(ModelicaInteger.class),
      new SimpleTypeSpec(ModelicaReal.class)
    };
  };


  public abc(ModelicaInteger a,ModelicaInteger b,ModelicaReal c) throws ModelicaRecordException {
    super("test.abc",new String[]{"a","b","c"},a,b,c);
  }

  public abc(String recordName, Map map) throws ModelicaRecordException {
    super(recordName,map);
  }

  public abc(ModelicaObject o) throws ModelicaRecordException {
    super(o);
    if (!this.getRecordName().equals("test.abc"))
      throw new ModelicaRecordException("Record name mismatch");
  }

  public ModelicaInteger get_a() {return get("a", ModelicaInteger.class);}
  public void set_a(ModelicaInteger a) {put("a", a);}

  public ModelicaInteger get_b() {return get("b", ModelicaInteger.class);}
  public void set_b(ModelicaInteger b) {put("b", b);}

  public ModelicaReal get_c() {return get("c", ModelicaReal.class);}
  public void set_c(ModelicaReal c) {put("c", c);}

  public static abc parse(Reader r) throws ParseException, IOException {
    return ModelicaRecord.parse(r,abc.class,fieldTypeSpecs);
  }
}
