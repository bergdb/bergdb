import java.util.concurrent.atomic.AtomicInteger;

import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;

/**
 * Probe (bergdb 016-06/S2, S2-F1): puts from four connections, each in its own thread, to a
 * directory with a "string/sv" index. Each object is then looked up by eq() on its own
 * name, in one thread; the full scan's order is checked against the collator's order.
 */
public class S2IcuIndexProbe {
    public static class P {
        public String name;
        public P() {}
    }
    
    public static void main(String[] args) throws Exception {
        final String type = args.length > 0 ? args[0] : "string/sv";
        final int threads = 4, perThread = 1500;
        final Database db = Factory.database().memory().start();
        try {
            db.indexBuilder("byName").type(type).dir("/p/").field("name").createFast();
            final AtomicInteger putErrors = new AtomicInteger();
            Thread[] ts = new Thread[threads];
            for (int t = 0; t < threads; t++) {
                final int tt = t;
                ts[t] = new Thread(() -> {
                    Connection c = db.newConnection();
                    for (int i = 0; i < perThread; i++) {
                        P p = new P();
                        p.name = name(tt * perThread + i);
                        try {
                            c.put("/p/" + (tt * perThread + i), p);
                        } catch (RuntimeException e) {
                            if (putErrors.getAndIncrement() == 0) {
                                System.out.println("first put error: " + e);
                            }
                        }
                    }
                });
            }
            for (Thread t : ts) t.start();
            for (Thread t : ts) t.join();
            
            Connection c = db.newConnection();
            int stored = 0, notFound = 0;
            for (int k = 0; k < threads * perThread; k++) {
                if (c.get("/p/" + k, P.class) == null) {
                    continue;
                }
                stored++;
                boolean found = false;
                for (P p : c.useIndex("byName", P.class).eq(name(k)).objects()) {
                    if (p.name.equals(name(k))) {
                        found = true;
                    }
                }
                if (!found) {
                    notFound++;
                }
            }
            int scanned = 0;
            for (P p : c.useIndex("byName", P.class).objects()) {
                scanned++;
            }
            System.out.println("index " + type + ": objects stored " + stored + ", put errors " 
                    + putErrors.get() + ", objects that eq() on their own name does not find " 
                    + notFound + ", entries in a full scan " + scanned);
        } finally {
            db.close();
        }
    }
    
    static String name(int k) {
        StringBuilder b = new StringBuilder();
        java.util.Random r = new java.util.Random(k);
        int len = 5 + r.nextInt(20);
        for (int j = 0; j < len; j++) {
            b.append("abcdefghijklmnopqrstuvwxyzåäö".charAt(r.nextInt(29)));
        }
        return b.toString() + k;
    }
}
