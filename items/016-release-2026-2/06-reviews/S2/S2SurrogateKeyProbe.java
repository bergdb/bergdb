import java.util.ArrayList;
import java.util.List;

import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;

/**
 * Probe (bergdb 016-06/S2): keys and index names with a lone surrogate. The UTF-8 encoder
 * writes a lone surrogate as '?' (005-26).
 */
public class S2SurrogateKeyProbe {
    public static class P {
        public long v;
        public P() {}
        public P(long v) { this.v = v; }
    }
    
    public static void main(String[] args) throws Exception {
        final Database db = Factory.database().memory().start();
        try {
            Connection c = db.newConnection();
            c.put("/k/a\uD800", "first");
            c.put("/k/a?", "second");
            System.out.println("1. get(\"/k/a\\uD800\") after a put of \"/k/a?\": " + c.get("/k/a\uD800", String.class));
            List<String> keys = new ArrayList<String>();
            for (bergdb.pub.Kv<String> kv : c.usePrimary(String.class).dir("/k/").kvs()) {
                keys.add(kv.key());
            }
            System.out.println("   keys in /k/: " + keys);
            
            db.indexBuilder("i\uD800").type("long").dir("/p/").field("v").createFast();
            db.indexBuilder("i?").type("long").dir("/q/").field("v").createFast();
            c.put("/p/1", new P(1));
            c.put("/q/2", new P(2));
            List<String> a = new ArrayList<String>();
            for (bergdb.pub.Kv<P> kv : c.useIndex("i\uD800", P.class).kvs()) {
                a.add(kv.key());
            }
            List<String> b = new ArrayList<String>();
            for (bergdb.pub.Kv<P> kv : c.useIndex("i?", P.class).kvs()) {
                b.add(kv.key());
            }
            System.out.println("2. index \"i\\uD800\" on /p/: " + a + "; index \"i?\" on /q/: " + b);
        } finally {
            db.close();
        }
    }
}
