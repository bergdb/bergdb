import java.util.ArrayList;
import java.util.List;

import bergdb.pub.util.Clock;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;

/**
 * Probe (bergdb 016-06/S2): the transaction of createFast()'s index info is refused before
 * its go point (a clock out of range, bergdb 005-18); the clock then comes back.
 */
public class S2RefusedCreateProbe {
    public static class P {
        public long v;
        public P() {}
        public P(long v) { this.v = v; }
    }
    
    static volatile boolean bad = false;
    
    public static void main(String[] args) throws Exception {
        Clock clock = new Clock() {
            long t = 1_000_000_000L;
            public long getTime() {
                return bad ? -1 : t++;
            }
        };
        final Database db = Factory.database().memory().clock(clock).start();
        try {
            Connection c = db.newConnection();
            bad = true;
            try {
                db.indexBuilder("X").type("long").dir("/p/").field("v").createFast();
                System.out.println("createFast: ok");
            } catch (RuntimeException e) {
                System.out.println("createFast refused: " + e.getClass().getSimpleName());
            }
            bad = false;
            try {
                db.indexBuilder("X");
                System.out.println("indexBuilder(\"X\") again: ok");
            } catch (RuntimeException e) {
                System.out.println("indexBuilder(\"X\") again throws " + e);
            }
            try {
                c.useIndex("X", P.class);
                System.out.println("useIndex(\"X\"): ok");
            } catch (RuntimeException e) {
                System.out.println("useIndex(\"X\") throws " + e.getClass().getSimpleName());
            }
            c.put("/p/1", new P(1));
            List<String> entries = new ArrayList<String>();
            for (bergdb.pub.Kv<byte[]> kv : c.usePrimary(byte[].class).kvs()) {
                if (kv.ikey().startsWith("/#i/di/")) entries.add(kv.ikey().substring(0, 12) + "...");
            }
            System.out.println("index entries in the database after a put to /p/: " + entries);
        } finally {
            db.close();
        }
    }
}
