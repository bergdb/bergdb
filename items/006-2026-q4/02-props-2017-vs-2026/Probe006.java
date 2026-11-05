import java.lang.management.ManagementFactory;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Random;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.management.ObjectName;

import bergdb.common.Bytes;
import bergdb.core.Db;
import bergdb.core.Trans;
import bergdb.dag.Keys;
import bergdb.pub.TestClock;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.DummyStream;
import bergdb.stream.MemoryStream;

/**
 * 006-02: Props's MEM and SS and Core's "set" test with a chosen startup distance,
 * compiled against the 2017 or the 2026 code. The default startup distance was 20 MB
 * in 2017 and is 50 MB since 2026-10-13; this separates that change of a default from
 * the changes of the code. The scenarios are copies of bergdb.dev.props.Mem, SS1 to SS4
 * and of bergdb.test.Set.run(100000, false, 2) as Core runs it; the only change is the
 * builder's startupDistance.
 *
 *   java Probe006 mem DISTANCE    MEM, bytes of heap per KV with one million small KVs
 *   java Probe006 histo DISTANCE  MEM's database: the live objects that its million KVs
 *                                 add, per class (the JVM's class histogram, before and
 *                                 after), in bytes and objects per KV
 *   java Probe006 ss DISTANCE     the four SS scenarios, printed as Props prints SS
 *   java Probe006 set DISTANCE    Core's set: the best of 5, normalized by 5.0e-6 s
 */
public class Probe006 {

    public static void main(String[] args) {
        String mode = args[0];
        int distance = Integer.parseInt(args[1]);
        if (mode.equals("mem")) {
            mem(distance);
        } else if (mode.equals("histo")) {
            histo(distance);
        } else if (mode.equals("ss")) {
            ss(distance);
        } else if (mode.equals("set")) {
            set(distance);
        } else {
            throw new IllegalArgumentException("mode: " + mode);
        }
    }

    // ---- MEM ----

    /** Mem.go: one million KVs, keys "0" to "999999", empty values, 100 per transaction. */
    static void mem(int distance) {
        int n = 1000 * 1000;
        Db db = Db.builder().testSetup().mainStream(new DummyStream())
                .startupDistance(distance).start();
        long emptyMem = usedMem();
        int batchSize = 100;
        for (int i = 0; i < n / batchSize; i++) {
            Trans.Builder b = db.trans();
            for (int j = 0; j < batchSize; j++) {
                b.put("" + (i * batchSize + j), new byte[0]);
            }
            db.execute(b.build());
        }
        long fullMem = usedMem();
        System.out.println(String.format(Locale.US, "MEM:%.0f startupDistance=%d",
                (double) (fullMem - emptyMem) / n, distance));
        db.stop();
    }

    /** As Mem.usedMem (Mem.go calls System.gc() three times more before each call). */
    static long usedMem() {
        Runtime rt = Runtime.getRuntime();
        for (int i = 0; i < 6; i++) {
            System.gc();
        }
        return rt.totalMemory() - rt.freeMemory();
    }

    /** The database of mem(), with a class histogram before and after the KVs. */
    static void histo(int distance) {
        int n = 1000 * 1000;
        Db db = Db.builder().testSetup().mainStream(new DummyStream())
                .startupDistance(distance).start();
        Map<String, long[]> before = histogram();
        int batchSize = 100;
        for (int i = 0; i < n / batchSize; i++) {
            Trans.Builder b = db.trans();
            for (int j = 0; j < batchSize; j++) {
                b.put("" + (i * batchSize + j), new byte[0]);
            }
            db.execute(b.build());
        }
        Map<String, long[]> after = histogram();
        final Map<String, long[]> delta = new HashMap<String, long[]>();
        long total = 0;
        for (Map.Entry<String, long[]> e : after.entrySet()) {
            long[] b = before.get(e.getKey());
            long[] d = new long[] {e.getValue()[0] - (b == null ? 0 : b[0]),
                                   e.getValue()[1] - (b == null ? 0 : b[1])};
            delta.put(e.getKey(), d);
            total += d[1];
        }
        List<String> names = new ArrayList<String>(delta.keySet());
        Collections.sort(names, new Comparator<String>() {
            public int compare(String a, String b) {
                return Long.compare(delta.get(b)[1], delta.get(a)[1]);
            }
        });
        System.out.println(String.format(Locale.US,
                "HISTO: %.1f bytes per KV in all classes, startupDistance=%d",
                (double) total / n, distance));
        for (int i = 0; i < 15 && i < names.size(); i++) {
            long[] d = delta.get(names.get(i));
            System.out.println(String.format(Locale.US, "  %7.1f bytes, %5.2f objects per KV  %s",
                    (double) d[1] / n, (double) d[0] / n, names.get(i)));
        }
        db.stop();
    }

    /** Class name: {instances, bytes}, of the live objects (GC.class_histogram). */
    static Map<String, long[]> histogram() {
        String text;
        try {
            text = (String) ManagementFactory.getPlatformMBeanServer().invoke(
                    new ObjectName("com.sun.management:type=DiagnosticCommand"),
                    "gcClassHistogram", new Object[] {new String[0]},
                    new String[] {String[].class.getName()});
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
        Map<String, long[]> result = new HashMap<String, long[]>();
        Matcher m = Pattern.compile("(?m)^\\s*\\d+:\\s+(\\d+)\\s+(\\d+)\\s+(\\S+)").matcher(text);
        while (m.find()) {
            result.put(m.group(3), new long[] {Long.parseLong(m.group(1)), Long.parseLong(m.group(2))});
        }
        return result;
    }

    // ---- SS ----

    static void ss(int distance) {
        double f1 = ss(distance, 10, 990, 100, 100 * 1000);   // SS1
        double f2 = ss(distance, 10, 990, 1, 100 * 1000);     // SS2
        double f3 = ss(distance, 10, 90, 100, 1000 * 1000);   // SS3
        double f4 = ss(distance, 10, 90, 1, 1000 * 1000);     // SS4
        double geo = Math.pow(f1 * f2 * f3 * f4, 1.0 / 4.0);
        System.out.println(String.format(Locale.US,
                "SS:%.2f (%.2f, %.2f, %.2f, %.2f) startupDistance=%d",
                geo, f1, f2, f3, f4, distance));
    }

    /** SS1's scenario with the given parameters (SS1 does not stop its Db either). */
    static double ss(int distance, int keySize, int valueSize, int kvsPerTrans, int kvCount) {
        int transCount = kvCount / kvsPerTrans;
        MemoryStream stream = new MemoryStream();
        Db db = Db.builder().mainStream(stream).startupDistance(distance).start();
        int counter = 0;
        for (int i = 0; i < transCount; i++) {
            Trans.Builder b = db.trans();
            for (int j = 0; j < kvsPerTrans; j++) {
                long[] key = Keys.toSegments("k-" + counter);
                b.put(key, new byte[valueSize]);
                counter++;
            }
            db.execute(b.build());
        }
        db.sync(SyncLevel.ORDINARY);
        long length = db.getStreamLength();
        long dataSize = (long) transCount * kvsPerTrans * (keySize + valueSize);
        double factor = ((double) length) / dataSize;
        System.out.println(String.format(Locale.US,
                "  kv size %d, %d per trans: stream length %d, factor %.4f",
                keySize + valueSize, kvsPerTrans, length, factor));
        return factor;
    }

    // ---- set ----

    static void set(int distance) {
        double best = Double.MAX_VALUE;
        for (int r = 0; r < 5; r++) {
            double t = setOnce(distance);
            best = Math.min(best, t);
            System.out.println(String.format(Locale.US, "  set run %d: %.3f us", r + 1, 1e6 * t));
        }
        System.out.println(String.format(Locale.US,
                "set:%.2f (best %.3f us per transaction) startupDistance=%d",
                best / 5.0e-6, 1e6 * best, distance));
    }

    static Db createSetDb(int distance) {
        return Db.builder()
                .clock(new TestClock())
                .noEvict()
                .stream("main", new DummyStream())
                .startupDistance(distance)
                .start();
    }

    /** Set.run(100000, false, 2): warm-up on one Db, then the timed loop on a new one. */
    static double setOnce(int distance) {
        Db db = createSetDb(distance);
        Random random = new Random(1);
        int n = 100 * 1000;
        Trans[] ts = new Trans[n];
        byte[] empty = new byte[0];
        byte[] bytes = new byte[4];
        for (int i = 0; i < n; i++) {
            Bytes.intToBytesBE(random.nextInt(), bytes, 0);
            ts[i] = db.trans().put(Keys.toSegments(bytes), empty).build();
        }
        for (int i = 0; i < n / 2; i++) {
            db.execute(ts[i]);
        }
        db = createSetDb(distance);
        long t0 = System.nanoTime();
        for (int r = 0; r < 2; r++) {
            for (int i = 0; i < n; i++) {
                db.execute(ts[i]);
            }
        }
        long t1 = System.nanoTime();
        return (t1 - t0) * 1e-9 / (2.0 * n);
    }
}
