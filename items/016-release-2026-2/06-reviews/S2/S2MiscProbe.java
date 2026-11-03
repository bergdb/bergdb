import java.util.ArrayList;
import java.util.List;

import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;

/**
 * Probe (bergdb 016-06/S2): an index with the same directory given twice; a class whose
 * no-argument constructor throws on its second call.
 */
public class S2MiscProbe {
    public static class P {
        public long v;
        public P() {}
        public P(long v) { this.v = v; }
    }
    public static class Fragile {
        static int calls = 0;
        public long v;
        public Fragile() {
            calls++;
            if (calls == 3) {
                throw new IllegalStateException("third construction");
            }
        }
    }
    
    public static void main(String[] args) throws Exception {
        final Database db = Factory.database().memory().start();
        try {
            db.indexBuilder("byV").type("long").dir("/p/").dir("/p/").field("v").createFast();
            Connection c = db.newConnection();
            c.put("/p/1", new P(1));
            List<String> keys = new ArrayList<String>();
            for (bergdb.pub.Kv<P> kv : c.useIndex("byV", P.class).kvs()) {
                keys.add(kv.key());
            }
            System.out.println("1. dir(\"/p/\") twice, one object: " + keys);
            
            Fragile f = new Fragile();   // call 1
            f.v = 7;
            c.put("/o/f", f);
            System.out.println("2. calls before the first get: " + Fragile.calls);
            for (int i = 0; i < 3; i++) {
                try {
                    System.out.println("   get " + i + ": " + c.get("/o/f", Fragile.class).v + ", calls " + Fragile.calls);
                } catch (Throwable e) {
                    System.out.println("   get " + i + " throws " + e.getClass().getName() + ": " + e.getMessage());
                }
            }
        } finally {
            db.close();
        }
    }
}
