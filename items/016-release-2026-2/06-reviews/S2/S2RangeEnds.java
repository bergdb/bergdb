import java.util.ArrayList;
import java.util.List;

import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;

/**
 * Probe (bergdb 016-06/S2): long and double index scans at the ends of their ranges, and an
 * int field in a long index.
 */
public class S2RangeEnds {
    public static class P {
        public long v;
        public double d;
        public P() {}
    }
    public static class Q {
        public int v;
        public Q() {}
    }
    
    static final long[] LONGS = {Long.MIN_VALUE, Long.MIN_VALUE + 1, -(1L << 62), -256, -255, -1, 0, 1, 255, 256, 
            1L << 56, 1L << 62, Long.MAX_VALUE - 1, Long.MAX_VALUE};
    static final double[] DOUBLES = {Double.NEGATIVE_INFINITY, -Double.MAX_VALUE, -1.5, -Double.MIN_VALUE, -0.0, 0.0,
            Double.MIN_VALUE, 1e-300, 1.5, Double.MAX_VALUE, Double.POSITIVE_INFINITY};
    
    public static void main(String[] args) throws Exception {
        final Database db = Factory.database().memory().start();
        try {
            db.indexBuilder("byV").type("long").dir("/p/").dir("/q/").field("v").createFast();
            db.indexBuilder("byD").type("double").dir("/p/").field("d").createFast();
            Connection c = db.newConnection();
            for (int i = 0; i < LONGS.length; i++) {
                P p = new P();
                p.v = LONGS[i];
                p.d = DOUBLES[i % DOUBLES.length];
                c.put("/p/" + i, p);
            }
            Q q = new Q();
            q.v = 7;
            c.put("/q/x", q);
            
            System.out.println("long scan: " + longs(c.useIndex("byV", P.class).objects()));
            System.out.println("long backward: " + longs(c.useIndex("byV", P.class).backward().objects()));
            System.out.println("startAt(MAX) excl: " + longs(c.useIndex("byV", P.class).startAt(Long.MAX_VALUE).inclusive(false).objects()));
            System.out.println("startAt(MAX) incl: " + longs(c.useIndex("byV", P.class).startAt(Long.MAX_VALUE).objects()));
            System.out.println("startAt(MIN) backward incl: " + longs(c.useIndex("byV", P.class).startAt(Long.MIN_VALUE).backward().objects()));
            System.out.println("startAt(MIN) backward excl: " + longs(c.useIndex("byV", P.class).startAt(Long.MIN_VALUE).backward().inclusive(false).objects()));
            System.out.println("eq(MAX) backward: " + longs(c.useIndex("byV", P.class).eq(Long.MAX_VALUE).backward().objects()));
            System.out.println("eq(7) (int field in /q/): " + longs(c.useIndex("byV", P.class).eq(7).objects()));
            List<Double> ds = new ArrayList<Double>();
            for (P p : c.useIndex("byD", P.class).objects()) {
                ds.add(p.d);
            }
            System.out.println("double scan: " + ds);
            ds.clear();
            for (P p : c.useIndex("byD", P.class).startAt(0.0).inclusive(false).objects()) {
                ds.add(p.d);
            }
            System.out.println("double startAt(0.0) excl: " + ds);
        } finally {
            db.close();
        }
    }
    
    static List<Long> longs(Iterable<P> it) {
        List<Long> list = new ArrayList<Long>();
        for (P p : it) {
            list.add(p.v);
        }
        return list;
    }
}
