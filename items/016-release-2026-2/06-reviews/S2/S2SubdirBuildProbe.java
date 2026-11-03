import java.util.ArrayList;
import java.util.List;

import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;

/**
 * Probe (bergdb 016-06/S2): an index on /p/ built with start(), with objects in /p/ and in
 * its subdirectory /p/q/; then writes to both.
 */
public class S2SubdirBuildProbe {
    public static class P {
        public long v;
        public P() {}
        public P(long v) { this.v = v; }
    }
    
    public static void main(String[] args) throws Exception {
        final Database db = Factory.database().memory().start();
        try {
            Connection c = db.newConnection();
            c.put("/p/1", new P(1));
            c.put("/p/q/2", new P(2));
            db.indexBuilder("byV").type("long").dir("/p/").field("v").start().join();
            System.out.println("after the build: " + kvs(c, null));
            c.put("/p/q/2", new P(5));
            c.put("/p/q/3", new P(3));
            c.put("/p/4", new P(4));
            System.out.println("after /p/q/2 := 5, /p/q/3 := 3, /p/4 := 4: " + kvs(c, null) 
                    + "; eq(2): " + kvs(c, 2L) + "; eq(5): " + kvs(c, 5L));
        } finally {
            db.close();
        }
    }
    
    static List<String> kvs(Connection c, Long eq) {
        List<String> list = new ArrayList<String>();
        Iterable<bergdb.pub.Kv<P>> it = eq == null ? c.useIndex("byV", P.class).kvs() 
                : c.useIndex("byV", P.class).eq(eq).kvs();
        for (bergdb.pub.Kv<P> kv : it) {
            list.add(kv.key() + "=" + kv.value().v);
        }
        return list;
    }
}
