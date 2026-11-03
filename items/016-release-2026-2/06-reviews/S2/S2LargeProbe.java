import java.util.Arrays;

import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;

/**
 * Probe (bergdb 016-06/S2): large values in an object, put and read back.
 */
public class S2LargeProbe {
    public static class P {
        public String s;
        public byte[] b;
        public long[] l;
        public P() {}
    }
    
    public static void main(String[] args) throws Exception {
        final Database db = Factory.database().memory().start();
        try {
            Connection c = db.newConnection();
            int[] sizes = {1 << 20, 10 << 20, 40 << 20};
            for (int size : sizes) {
                P p = new P();
                char[] cs = new char[size / 4];
                Arrays.fill(cs, 'é');
                p.s = new String(cs);
                p.b = new byte[size / 2];
                p.b[p.b.length - 1] = 7;
                p.l = new long[size / 64];
                p.l[p.l.length - 1] = Long.MIN_VALUE;
                try {
                    c.put("/o/" + size, p);
                    P r = c.get("/o/" + size, P.class);
                    System.out.println(size + " bytes or so: read back equal: " + (r.s.equals(p.s) 
                            && Arrays.equals(r.b, p.b) && Arrays.equals(r.l, p.l)));
                } catch (Throwable e) {
                    System.out.println(size + " bytes or so: " + e.getClass().getName() + ": " 
                            + String.valueOf(e.getMessage()).split("\n")[0]);
                }
            }
            System.out.println("the database after them: " + c.get("/o/" + sizes[0], P.class).b.length);
        } finally {
            db.close();
        }
    }
}
