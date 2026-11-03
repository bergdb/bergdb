import java.util.ArrayList;
import java.util.List;

import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.Kv;

/**
 * Probe (bergdb 016-06/S2): usePrimary() with startAt() before and after dir(), and without
 * dir(), in a database with one index.
 */
public class S2PrimaryProbe {
    public static class P {
        public long v;
        public P() {}
        public P(long v) { this.v = v; }
    }
    
    public static void main(String[] args) throws Exception {
        final Database db = Factory.database().memory().start();
        try {
            db.indexBuilder("byV").type("long").dir("/p/").field("v").createFast();
            Connection c = db.newConnection();
            for (int i = 1; i <= 5; i++) {
                c.put("/p/" + i, new P(i));
            }
            System.out.println("dir(\"/p/\").startAt(\"3\"): " + keys(c.usePrimary(P.class).dir("/p/").startAt("3").kvs()));
            System.out.println("startAt(\"3\").dir(\"/p/\"): " + keys(c.usePrimary(P.class).startAt("3").dir("/p/").kvs()));
            System.out.println("no dir(), P.class: " + keys(c.usePrimary(P.class).kvs()));
            List<String> raw = new ArrayList<String>();
            for (Kv<byte[]> kv : c.usePrimary(byte[].class).kvs()) {
                raw.add(kv.key() + "|" + kv.ikey());
            }
            System.out.println("no dir(), byte[].class: " + raw);
        } finally {
            db.close();
        }
    }
    
    static List<String> keys(Iterable<Kv<P>> it) {
        List<String> list = new ArrayList<String>();
        for (Kv<P> kv : it) {
            list.add(kv.key() + "|" + kv.ikey());
        }
        return list;
    }
}
