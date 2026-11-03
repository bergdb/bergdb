import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;

/**
 * Probe (bergdb 016-06/S2): fields of common JDK and enum types, put and read back.
 */
public class S2JdkFieldsProbe {
    public enum Color { RED, GREEN }
    public static class WithDate { public java.util.Date x; public WithDate() {} }
    public static class WithEnum { public Color x; public WithEnum() {} }
    public static class WithInstant { public java.time.Instant x; public WithInstant() {} }
    
    public static void main(String[] args) throws Exception {
        final Database db = Factory.database().memory().start();
        try {
            Connection c = db.newConnection();
            WithDate d = new WithDate();
            d.x = new java.util.Date(0);
            try {
                c.put("/o/date", d);
                Thread.sleep(5);
                System.out.println("1. Date(0) read back: " + c.get("/o/date", WithDate.class).x.getTime() + " ms since 1970");
            } catch (Throwable e) {
                System.out.println("1. Date: " + e);
            }
            WithEnum e1 = new WithEnum();
            e1.x = Color.GREEN;
            try {
                c.put("/o/enum", e1);
                System.out.println("2. enum GREEN put: ok");
                System.out.println("   read back: " + c.get("/o/enum", WithEnum.class).x);
            } catch (Throwable e) {
                System.out.println("   " + e);
            }
            WithInstant i = new WithInstant();
            i.x = java.time.Instant.ofEpochSecond(42);
            try {
                c.put("/o/instant", i);
                System.out.println("3. Instant put: ok");
                System.out.println("   read back: " + c.get("/o/instant", WithInstant.class).x);
            } catch (Throwable e) {
                System.out.println("   " + e);
            }
        } finally {
            db.close();
        }
    }
}
