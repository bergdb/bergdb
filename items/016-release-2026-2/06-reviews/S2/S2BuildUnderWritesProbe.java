import java.util.HashMap;
import java.util.Map;
import java.util.Random;

import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.Kv;
import bergdb.pub.util.JobStatus;

/**
 * Probe (bergdb 016-06/S2): an index built with start() while two threads update, delete
 * and add objects in its directory; afterwards the index must hold exactly one entry per
 * object, at its value.
 */
public class S2BuildUnderWritesProbe {
    public static class P {
        public long v;
        public P() {}
        public P(long v) { this.v = v; }
    }
    
    public static void main(String[] args) throws Exception {
        final Database db = Factory.database().memory().start();
        try {
            final int n = 3000;
            Connection c0 = db.newConnection();
            for (int i = 0; i < n; i++) {
                c0.put("/p/" + i, new P(i));
            }
            final long end = System.nanoTime() + 3_000_000_000L;
            Thread[] ws = new Thread[2];
            for (int t = 0; t < ws.length; t++) {
                final int seed = t;
                ws[t] = new Thread(() -> {
                    Random r = new Random(seed);
                    Connection c = db.newConnection();
                    while (System.nanoTime() < end) {
                        int k = r.nextInt(n + 500);
                        if (r.nextInt(5) == 0) {
                            c.delete("/p/" + k);
                        } else {
                            c.put("/p/" + k, new P(r.nextInt(100000)));
                        }
                    }
                });
            }
            for (Thread w : ws) w.start();
            JobStatus st = db.indexBuilder("byV").type("long").dir("/p/").field("v").start().join();
            for (Thread w : ws) w.join();
            
            Map<String, Long> data = new HashMap<String, Long>();
            for (Kv<P> kv : c0.usePrimary(P.class).dir("/p/").kvs()) {
                data.put(kv.key(), kv.value().v);
            }
            Map<String, Integer> entries = new HashMap<String, Integer>();
            int wrongValue = 0, scanned = 0;
            long last = Long.MIN_VALUE;
            int outOfOrder = 0;
            for (Kv<P> kv : c0.useIndex("byV", P.class).kvs()) {
                scanned++;
                entries.merge(kv.key(), 1, Integer::sum);
                if (kv.value().v < last) outOfOrder++;
                last = kv.value().v;
            }
            int missing = 0, doubled = 0;
            for (String k : data.keySet()) {
                Integer e = entries.get(k);
                if (e == null) missing++;
                else if (e > 1) doubled++;
            }
            for (Map.Entry<String, Long> e : data.entrySet()) {
                boolean found = false;
                for (P p : c0.useIndex("byV", P.class).eq(e.getValue()).objects()) {
                    if (p.v == e.getValue()) found = true;
                }
                if (!found) wrongValue++;
            }
            System.out.println("build: " + st.progress() + "; objects " + data.size() + ", entries scanned " + scanned
                    + ", objects without an entry " + missing + ", with two or more " + doubled
                    + ", not found by eq(own value) " + wrongValue + ", out of order " + outOfOrder);
        } finally {
            db.close();
        }
    }
}
