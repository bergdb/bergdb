import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;

/**
 * Probe (bergdb 016-06/S2): a subclass whose field hides a field of the same name in its
 * superclass.
 */
public class S2HiddenFieldProbe {
    public static class Base { public long x; public Base() {} }
    public static class Sub extends Base { public long x; public Sub() {} }
    
    public static void main(String[] args) throws Exception {
        final Database db = Factory.database().memory().start();
        try {
            Connection c = db.newConnection();
            Sub s = new Sub();
            s.x = 1;
            ((Base) s).x = 2;
            c.put("/o/s", s);
            Sub r = c.get("/o/s", Sub.class);
            System.out.println("Sub.x = 1, Base.x = 2; read back: Sub.x = " + r.x + ", Base.x = " + ((Base) r).x);
        } finally {
            db.close();
        }
    }
}
