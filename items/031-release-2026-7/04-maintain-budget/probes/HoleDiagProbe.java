package bergdb.core;

import java.util.TreeMap;
import java.util.concurrent.atomic.AtomicLong;
import bergdb.dag.Keys;
import bergdb.dag.Node;
import bergdb.dag.ValueNode;
import bergdb.pub.util.Clock;
import bergdb.stream.MemoryStream;

/**
 * bergdb 031-04: where the stream kept goes in HoleProbe's case on the prototype. As
 * HoleProbe N1 N2 (one database), and the records after the second writes summed by kind:
 * the application's, a step's, a table's (with the take's index nodes), the row's.
 *   java -cp out:bergdb.jar bergdb.core.HoleDiagProbe N1 N2 [SD]
 */
public class HoleDiagProbe {
    static final AtomicLong clock = new AtomicLong(1_778_000_000_000L * 10_000L);
    static final TreeMap<String, long[]> kinds = new TreeMap<>();
    static boolean on = false;

    static void exec(Db db, Trans.Builder b) {
        clock.addAndGet(10_000);
        db.execute(b.build());
    }

    static void fill(Db db, int n, String p, boolean delete) {
        for (int i = 0; i < n; i += 100) {
            Trans.Builder b = db.trans();
            for (int k = i; k < i + 100 && k < n; k++) {
                if (delete) b.delete(p + k); else b.put(p + k, new byte[100]);
            }
            exec(db, b);
        }
    }

    public static void main(String[] a) throws Exception {
        final int n1 = Integer.parseInt(a[0]), n2 = Integer.parseInt(a[1]);
        final int sd = a.length > 2 ? Integer.parseInt(a[2]) : 5000000;
        Db db = Db.builder().mainStream(new MemoryStream()).clock(clock::get).start();
        Db.testHooks = new Db.TestHooks() {
            public void transExecuted(Db.ExecuteData x) {
                if (!on) return;
                String kind = !x.trans.isInternal ? "app" : x.trans.touch ? "step" : "internal";
                if (x.transNodes.valueCount > 0) {
                    kind += " " + Keys.toString(x.transNodes.keys[0]);
                }
                long[] c = kinds.computeIfAbsent(kind, k -> new long[3]);
                c[0]++;
                c[1] += x.trans.nextPos - x.trans.tpos;
                c[2] += x.transNodes.keyCount;
            }
            public void valueNodeCreated(ValueNode n, long[] k) {}
            public void nodeTouched(Node n) {}
            public void nodeReplaced(Node n) {}
        };
        db.setRetainDuration(Clock.UNITS_PER_SEC);
        db.setStartupDistance(sd);
        fill(db, n1, "/k/", false);
        fill(db, n1, "/k/", true);
        for (int i = 0; i < 5000; i++) {
            clock.addAndGet(10_000);
            M.call(db);
            Reclaim.IterationInfo last = db.internal().reclaim().currentIteration();
            if (last == null && db.internal().reclaim().getIterationCount() > 0) break;
        }
        fill(db, n2, "/m/", false);
        fill(db, n2, "/m/", true);
        final long p0 = db.getStreamLength();
        on = true;
        for (int j = 0; j < 10000; j++) {
            clock.addAndGet(10_000);
            M.call(db);
        }
        System.out.println("after the second writes " + p0 + "; fp " + db.getFirstAvailablePos()
                + ", kept " + (db.getStreamLength() - db.getFirstAvailablePos()) + ", sp "
                + db.internal().getStartupPosForEvict());
        for (java.util.Map.Entry<String, long[]> e : kinds.entrySet()) {
            System.out.println(String.format("  %-40s records %6d bytes %9d index nodes %7d",
                    e.getKey(), e.getValue()[0], e.getValue()[1], e.getValue()[2]));
        }
        db.close();
    }
}
