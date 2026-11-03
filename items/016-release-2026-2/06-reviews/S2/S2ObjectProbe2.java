import java.util.Arrays;

import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;

/**
 * Probe (bergdb 016-06/S2): Java types at their limits, empty and null values; and stored
 * values that are not numbers read into a primitive field, as after a change of the class.
 */
public class S2ObjectProbe2 {
    public static class Inner { public int a = 1; public Inner() {} }
    public static class All {
        public byte b; public short s; public char c; public int i; public long l; public float f; public double d;
        public boolean z; public String str; public byte[] bytes; public int[] ints; public String[] strs;
        public Inner inner; public Integer boxed; public long[][] nested;
        public All() {}
    }
    public static class WithInner { public Inner x; public WithInner() {} }
    public static class WithBoxed { public Integer x; public WithBoxed() {} }
    public static class WithBytes { public byte[] x; public WithBytes() {} }
    public static class WithInt { public int x = 5; public WithInt() {} }
    
    public static void main(String[] args) throws Exception {
        final Database db = Factory.database().memory().start();
        try {
            Connection c = db.newConnection();
            All a = new All();
            a.b = Byte.MIN_VALUE; a.s = Short.MIN_VALUE; a.c = Character.MAX_VALUE; a.i = Integer.MIN_VALUE;
            a.l = Long.MIN_VALUE; a.f = Float.NaN; a.d = -0.0; a.z = true; a.str = ""; a.bytes = new byte[0];
            a.ints = new int[0]; a.strs = new String[] {null, "", "😀"}; a.inner = null; a.boxed = null;
            a.nested = new long[][] {{Long.MAX_VALUE}, {}, null};
            c.put("/o/all", a);
            All r = c.get("/o/all", All.class);
            System.out.println("1. limits: b " + r.b + ", s " + r.s + ", c " + (int) r.c + ", i " + r.i + ", l " + r.l 
                    + ", f " + r.f + ", d " + r.d + ", z " + r.z + ", str '" + r.str + "', bytes " + Arrays.toString(r.bytes)
                    + ", ints " + Arrays.toString(r.ints) + ", strs " + Arrays.toString(r.strs) + ", inner " + r.inner
                    + ", boxed " + r.boxed + ", nested " + Arrays.deepToString(r.nested));
            
            WithInner wi = new WithInner();
            wi.x = new Inner();
            c.put("/o/inner", wi);
            WithBoxed wb = new WithBoxed();
            c.put("/o/boxed", wb);
            WithBytes wy = new WithBytes();
            wy.x = new byte[] {1, 2};
            c.put("/o/bytes", wy);
            String[] keys = {"/o/inner", "/o/boxed", "/o/bytes"};
            String[] what = {"a nested object", "a null Integer", "a byte[]"};
            for (int k = 0; k < keys.length; k++) {
                try {
                    System.out.println("2. " + what[k] + " read into an int field: " + c.get(keys[k], WithInt.class).x);
                } catch (Throwable e) {
                    System.out.println("2. " + what[k] + " read into an int field throws " + e.getClass().getName() 
                            + ": " + String.valueOf(e.getMessage()).split("\n")[0]);
                }
            }
            System.out.println("   the database after them: get " + c.get("/o/all", All.class).i);
        } finally {
            db.close();
        }
    }
}
