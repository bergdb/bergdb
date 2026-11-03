import java.util.ArrayList;
import java.util.List;

import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;

/**
 * Probe (bergdb 016-06/S2): a composite index (long a, long b); eq() and startAt() on the
 * second level without a condition on the first.
 */
public class S2NextLevelProbe {
    public static class P {
        public long a, b;
        public P() {}
        public P(long a, long b) { this.a = a; this.b = b; }
    }
    
    public static void main(String[] args) throws Exception {
        final Database db = Factory.database().memory().start();
        try {
            db.indexBuilder("ab").dir("/p/").type("long").field("a").type("long").field("b").createFast();
            Connection c = db.newConnection();
            c.put("/p/1", new P(1, 5));
            c.put("/p/2", new P(5, 1));
            c.put("/p/3", new P(2, 7));
            try {
                System.out.println("nextLevel().eq(5): " + list(c.useIndex("ab", P.class).nextLevel().eq(5).objects()));
            } catch (RuntimeException e) {
                System.out.println("nextLevel().eq(5) refused: " + e);
            }
            try {
                System.out.println("nextLevel().startAt(7): " + list(c.useIndex("ab", P.class).nextLevel().startAt(7).objects()));
            } catch (RuntimeException e) {
                System.out.println("nextLevel().startAt(7) refused: " + e);
            }
        } finally {
            db.close();
        }
    }
    
    static List<String> list(Iterable<P> it) {
        List<String> list = new ArrayList<String>();
        for (P p : it) {
            list.add("(" + p.a + "," + p.b + ")");
        }
        return list;
    }
}
