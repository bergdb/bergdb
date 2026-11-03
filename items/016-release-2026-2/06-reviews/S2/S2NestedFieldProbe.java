import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;

/**
 * Probe (bergdb 016-06/S2): an index on a nested field spec with an empty part, which
 * nestedField() accepts, where field() refuses the empty string; then puts to its
 * directory. Also an Object field that holds an Integer.
 */
public class S2NestedFieldProbe {
    public static class Car { public Dim dimensions; public Car() {} }
    public static class Dim { public long length; public Dim() {} }
    public static class O { public Object x; public O() {} }
    
    public static void main(String[] args) throws Exception {
        for (String spec : new String[] {"dimensions..length", "dimensions.length."}) {
            final Database db = Factory.database().memory().start();
            try {
                try {
                    db.indexBuilder("byLength").type("long").dir("/cars/").nestedField(spec).createFast();
                    System.out.println("nestedField(\"" + spec + "\"): index created");
                } catch (Throwable e) {
                    System.out.println("nestedField(\"" + spec + "\") refused: " + e);
                    continue;
                }
                Connection c = db.newConnection();
                Car car = new Car();
                car.dimensions = new Dim();
                car.dimensions.length = 4;
                try {
                    c.put("/cars/1", car);
                    System.out.println("   put to /cars/: ok");
                } catch (Throwable e) {
                    System.out.println("   put to /cars/ throws " + e);
                }
                try {
                    c.put("/cars/2", "a string, no object");
                    c.put("/other/1", car);
                    System.out.println("   put of a String to /cars/, and of the object elsewhere: ok");
                } catch (Throwable e) {
                    System.out.println("   other puts throw " + e);
                }
            } finally {
                db.close();
            }
        }
        final Database db = Factory.database().memory().start();
        try {
            Connection c = db.newConnection();
            O o = new O();
            o.x = 5;
            c.put("/o/1", o);
            System.out.println("an Object field that holds Integer 5, read back: " + c.get("/o/1", O.class).x);
        } finally {
            db.close();
        }
    }
}
