import java.util.ArrayList;
import java.util.Arrays;

import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;

/**
 * Probe (bergdb 016-06/S2): values stored by put() of one class and read by get() into
 * another, as after a change of the class between a write and a read; and a few
 * values at their limits.
 */
public class S2ObjectProbe {
    public static class D { public double x; public D() {} }
    public static class S { public String x; public S() {} }
    public static class L { public long x; public L() {} }
    public static class I { public int x; public I() {} }
    public static class B { public boolean x; public B() {} }
    public static class A { public Object[] x; public A() {} }
    public static class F { public final long x; public long y; public F() { x = 0; } public F(long v) { x = v; y = v; } }
    public static class Li { public ArrayList<String> x; public Li() {} }
    
    public static void main(String[] args) throws Exception {
        final Database db = Factory.database().memory().start();
        try {
            Connection c = db.newConnection();
            
            D d = new D();
            d.x = 1.5;
            c.put("/o/d", d);
            System.out.println("1. double 1.5 read into a String field: '" + c.get("/o/d", S.class).x + "'");
            
            d.x = 9223372036854775808.0;   // 2^63, one above Long.MAX_VALUE
            c.put("/o/d2", d);
            try {
                System.out.println("2. double 2^63 read into a long field: " + c.get("/o/d2", L.class).x);
            } catch (RuntimeException e) {
                System.out.println("2. double 2^63 read into a long field throws " + e);
            }
            d.x = 2147483648.0;   // 2^31
            c.put("/o/d3", d);
            try {
                System.out.println("   double 2^31 read into an int field: " + c.get("/o/d3", I.class).x);
            } catch (RuntimeException e) {
                System.out.println("   double 2^31 read into an int field throws " + e.getClass().getSimpleName());
            }
            
            S s = new S();
            s.x = "123";
            c.put("/o/s", s);
            try {
                System.out.println("3. String \"123\" read into a long field: " + c.get("/o/s", L.class).x);
            } catch (RuntimeException e) {
                System.out.println("3. String read into a long field throws " + e);
            }
            B b = new B();
            b.x = true;
            c.put("/o/b", b);
            try {
                System.out.println("   boolean true read into an int field: " + c.get("/o/b", I.class).x);
            } catch (RuntimeException e) {
                System.out.println("   boolean read into an int field throws " + e);
            }
            
            A a = new A();
            a.x = new Object[] {1, "a", 2.5};
            c.put("/o/a", a);
            System.out.println("4. Object[]{1, \"a\", 2.5} read back: " + Arrays.toString(c.get("/o/a", A.class).x));
            
            a.x = new Object[1];
            a.x[0] = a.x;
            try {
                c.put("/o/a2", a);
                System.out.println("5. Object[] that holds itself: stored");
            } catch (Throwable e) {
                System.out.println("5. Object[] that holds itself: " + e.getClass().getName() 
                        + (e.getMessage() == null ? "" : ": " + e.getMessage()));
            }
            
            c.put("/o/f", new F(42));
            F f = c.get("/o/f", F.class);
            System.out.println("6. final long x = 42, long y = 42, read back: x = " + f.x + ", y = " + f.y);
            
            Li li = new Li();
            li.x = new ArrayList<String>(Arrays.asList("p", "q"));
            try {
                c.put("/o/li", li);
                Li got = c.get("/o/li", Li.class);
                System.out.println("7. ArrayList [p, q] read back: size " + got.x.size() + ", " + got.x);
            } catch (Throwable e) {
                System.out.println("7. ArrayList field: " + e.getClass().getName());
            }
        } finally {
            db.close();
        }
    }
}
