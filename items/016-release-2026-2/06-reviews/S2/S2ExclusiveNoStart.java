import java.util.ArrayList;
import java.util.List;

import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;

/**
 * Probe (bergdb 016-06/S2): inclusive(false) on a secondary index without startAt(), and
 * with eq(). No start value is given, so there is no exact match to exclude.
 */
public class S2ExclusiveNoStart {
    public static class P {
        public long v;
        public String s;
        public P() {}
    }
    
    public static void main(String[] args) throws Exception {
        final Database db = Factory.database().memory().start();
        try {
            db.indexBuilder("byV").type("long").dir("/p/").field("v").createFast();
            db.indexBuilder("byS").type("string").dir("/p/").field("s").createFast();
            db.indexBuilder("byVS").type("long").field("v").type("string").field("s").dir("/p/").createFast();
            Connection c = db.newConnection();
            for (int i = 1; i <= 5; i++) {
                P p = new P();
                p.v = i;
                p.s = "s" + i;
                c.put("/p/" + i, p);
            }
            print("long, forward, inclusive(true)  ", c.useIndex("byV", P.class).objects());
            print("long, forward, inclusive(false) ", c.useIndex("byV", P.class).inclusive(false).objects());
            print("long, backward, inclusive(true) ", c.useIndex("byV", P.class).backward().objects());
            print("long, backward, inclusive(false)", c.useIndex("byV", P.class).backward().inclusive(false).objects());
            print("string, forward, inclusive(false)", c.useIndex("byS", P.class).inclusive(false).objects());
            print("composite eq(3), inclusive(true) ", c.useIndex("byVS", P.class).eq(3).objects());
            print("composite eq(3), inclusive(false)", c.useIndex("byVS", P.class).eq(3).inclusive(false).objects());
            print("primary, forward, inclusive(false)", c.usePrimary(P.class).dir("/p/").inclusive(false).objects());
        } finally {
            db.close();
        }
    }
    
    static void print(String label, Iterable<P> it) {
        List<Long> list = new ArrayList<Long>();
        for (P p : it) {
            list.add(p.v);
        }
        System.out.println(label + ": " + list);
    }
}
