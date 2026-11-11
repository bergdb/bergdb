package bergdb.core;

import java.io.File;
import java.util.List;
import java.util.Random;
import java.util.TreeMap;

import bergdb.dag.Handle;
import bergdb.dag.KeyNode;
import bergdb.dag.Klong;
import bergdb.dag.Node;
import bergdb.dag.Pointee;
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;
import bergdb.stream.DummyStream;

/**
 * MEM's method (bergdb.dev.props.Mem; bergdb 006-02) at n KVs with a chosen key shape, and a
 * breakdown of the heap by structure and by class (bergdb 024-08).
 *
 * Usage: MemProbe n=1000000 keys=dec [order=asc|random] [value=0] [hist=FILE] [walk=1]
 *   keys=dec          "" + i, Mem's keys
 *   keys=off:K        "" + (i + K)
 *   keys=fmt:FORMAT   String.format(FORMAT, i), such as fmt:/k/%010d
 *   keys=rnd:L        L random chars of a to z and 0 to 9 (seeded), distinct with high chance
 *   keys=hex:L        L random hex chars
 * The setup is Mem's: testSetup() (test clock, no eviction, retain forever), a DummyStream,
 * 100 KVs a transaction.
 */
public class MemProbe {
    static long usedHeap() {
        Runtime rt = Runtime.getRuntime();
        for (int k = 0; k < 4; k++) System.gc();
        return rt.totalMemory() - rt.freeMemory();
    }

    static String arg(String[] args, String name, String def) {
        for (String a : args) if (a.startsWith(name + "=")) return a.substring(name.length() + 1);
        return def;
    }

    public static void main(String[] args) throws Exception {
        int n = Integer.parseInt(arg(args, "n", "1000000"));
        String keys = arg(args, "keys", "dec");
        String order = arg(args, "order", "asc");
        int valueSize = Integer.parseInt(arg(args, "value", "0"));
        String hist = arg(args, "hist", null);
        boolean walk = !"0".equals(arg(args, "walk", "1"));
        System.out.println("MemProbe n=" + n + " keys=" + keys + " order=" + order + " value="
                + valueSize + " java=" + System.getProperty("java.version")
                + " maxHeap=" + Runtime.getRuntime().maxMemory());

        // The order of the puts, made before the first heap reading and released after the fill.
        int[] perm = null;
        if (order.equals("random")) {
            perm = new int[n];
            for (int i = 0; i < n; i++) perm[i] = i;
            Random r = new Random(1);
            for (int i = n - 1; i > 0; i--) {
                int j = r.nextInt(i + 1);
                int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
            }
        }
        Random rnd = new Random(7);
        final String alpha = "abcdefghijklmnopqrstuvwxyz0123456789";
        final String hexs = "0123456789abcdef";

        // setup=mem (default): Mem's. setup=default dir=DIR: the builder's defaults on a
        // FileStream (eviction on, cache indicator 200 MB or cache=MB, startup distance 50 MB,
        // retain forever), as 024-03's probe but without a retain duration.
        String setup = arg(args, "setup", "mem");
        Db db;
        if (setup.equals("mem")) {
            db = Db.builder().testSetup().mainStream(new DummyStream()).start();
        } else {
            DbBuilder bu = Db.builder().mainStream(new bergdb.stream.FileStream(
                    new File(arg(args, "dir", null)))).clock(new CoreTestClock());
            String cache = arg(args, "cache", null);
            if (cache != null) bu.cacheSizeIndicator(Long.parseLong(cache) * 1000000);
            if ("1".equals(arg(args, "noevict", "0"))) bu.noEvict();
            db = bu.start();
        }
        System.out.println("setup=" + setup + " cacheSizeIndicator=" + db.getCacheSizeIndicator()
                + " startupDistance=" + db.getStartupDistance());
        long empty = usedHeap();
        String hist0 = arg(args, "hist0", null);
        if (hist0 != null) histogram(hist0);
        long t0 = System.nanoTime();
        long keyBytes = 0;
        for (int k = 0; k < n / 100; k++) {
            Trans.Builder b = db.trans();
            for (int j = 0; j < 100; j++) {
                int i = k * 100 + j;
                if (perm != null) i = perm[i];
                String key;
                if (keys.equals("dec")) key = "" + i;
                else if (keys.startsWith("off:")) key = "" + (i + Long.parseLong(keys.substring(4)));
                else if (keys.startsWith("fmt:")) key = String.format(keys.substring(4), i);
                else if (keys.startsWith("rnd:") || keys.startsWith("hex:")) {
                    String a = keys.startsWith("rnd:") ? alpha : hexs;
                    int len = Integer.parseInt(keys.substring(4));
                    char[] c = new char[len];
                    for (int q = 0; q < len; q++) c[q] = a.charAt(rnd.nextInt(a.length()));
                    key = new String(c);
                } else throw new IllegalArgumentException(keys);
                keyBytes += key.length();
                b.put(key, new byte[valueSize]);
            }
            db.execute(b.build());
        }
        long fillNs = System.nanoTime() - t0;
        perm = null;
        long full = usedHeap();
        long kvs = db.getKvCount();
        System.out.println(String.format("MEM n=%d keys=%s order=%s value=%d: %.1f bytes/KV"
                + " (heap %d - %d = %d bytes)", n, keys, order, valueSize,
                (double) (full - empty) / n, full, empty, full - empty));
        System.out.println(String.format("fill %.1f s, %.2f us/put; kvCount=%d; key bytes/KV %.2f;"
                + " stream %d bytes, %.1f bytes/KV; transactions %d; reclaim iterations %d",
                fillNs / 1e9, fillNs / 1e3 / n, kvs, (double) keyBytes / n, db.getStreamLength(),
                (double) db.getStreamLength() / n, db.getTransactionCount(),
                db.getReclaimIterationCount()));
        System.out.println("cacheStats: " + db.internal().cacheStats());

        if (walk) walk(db, n);
        int gets = Integer.parseInt(arg(args, "gets", "0"));
        if (gets > 0) {
            // Gets of keys of the fill: for rnd and hex the first 'gets' keys put, else keys
            // spread over 0..n-1. Twice; loads are the node versions read from the stream.
            for (int round = 1; round <= 2; round++) {
                Random r2 = new Random(7);
                long loads0 = db.internal().cacheStats().loads;
                long g0 = System.nanoTime();
                int found = 0;
                for (int g = 0; g < gets; g++) {
                    String key;
                    if (keys.startsWith("rnd:") || keys.startsWith("hex:")) {
                        String a = keys.startsWith("rnd:") ? alpha : hexs;
                        int len = Integer.parseInt(keys.substring(4));
                        char[] c = new char[len];
                        for (int q = 0; q < len; q++) c[q] = a.charAt(r2.nextInt(a.length()));
                        key = new String(c);
                    } else {
                        long i = (long) g * (n / gets);
                        if (keys.equals("dec")) key = "" + i;
                        else if (keys.startsWith("off:")) key = "" + (i + Long.parseLong(keys.substring(4)));
                        else key = String.format(keys.substring(4), i);
                    }
                    byte[] v = db.getOne(Long.MAX_VALUE, bergdb.dag.Keys.toSegments(
                            bergdb.dag.Keys.toBytes(key)), db.newGetData());
                    if (v != null) found++;
                }
                long gns = System.nanoTime() - g0;
                System.out.println(String.format("GETS round %d: %d gets, %d found, %.2f us/get,"
                        + " %.2f loads/get", round, gets, found, gns / 1e3 / gets,
                        (double) (db.internal().cacheStats().loads - loads0) / gets));
            }
            System.out.println("heap after the gets " + usedHeap() + "; cacheStats: "
                    + db.internal().cacheStats());
        }
        if (hist != null) histogram(hist);
        // The database is live until here.
        System.out.println("kvCount at the end " + db.getKvCount());
        db.stop();
    }

    /** A class histogram of the live objects (jcmd's GC.class_histogram: after a full GC). */
    static void histogram(String file) throws Exception {
        long pid = ProcessHandle.current().pid();
        String jcmd = System.getProperty("java.home") + "/bin/jcmd";
        Process p = new ProcessBuilder(jcmd, "" + pid, "GC.class_histogram")
                .redirectErrorStream(true).redirectOutput(new File(file)).start();
        p.waitFor();
        System.out.println("histogram in " + file);
    }

    static int align8(long x) { return (int) ((x + 7) & ~7L); }

    /** The node table's objects by structure; bytes by the JVM's layout (JDK 27 defaults:
     *  compact object headers, compressed oops), checked against the class histogram. */
    static void walk(Db db, int n) {
        List<Node> nodes = db.internal().cache().nodes();
        int handles = db.internal().cache().handles().size();
        long keyNodes = 0, leaves = 0, topNodes = 0, other = 0;
        // by capacity (klongs.length): nodes, used klongs
        TreeMap<Integer, long[]> byCap = new TreeMap<Integer, long[]>();
        long timeKlongs = 0, keyKlongs = 0, key7 = 0, keyShort = 0, delKlongs = 0;
        long pHandle = 0, pValue = 0, pNull = 0, valueBytes = 0;
        long oneKey = 0, oneKeyLeaf = 0;      // key nodes with exactly one key klong
        long keyArrays = 0;                   // bytes of klongs + pos + pointers arrays
        long oneKeyArrays = 0;
        long topBytes = 0;
        for (Node node : nodes) {
            if (node instanceof KeyNode) {
                KeyNode kn = (KeyNode) node;
                keyNodes++;
                if (kn.isSegmentLeaf()) leaves++;
                int size = kn.size;
                long[] kl = kn.klongs;
                Pointee[] ps = kn.pointers;
                long[] c = byCap.get(kl.length);
                if (c == null) { c = new long[2]; byCap.put(kl.length, c); }
                c[0]++; c[1] += size;
                int arr = (16 + 8 * kl.length) + (16 + 8 * kn.pos.length)
                        + align8(12 + 4L * ps.length);
                keyArrays += arr;
                int keysHere = 0;
                for (int i = 0; i < size; i++) {
                    long k = kl[i];
                    if (Klong.isTime(k)) { timeKlongs++; continue; }
                    if (Klong.isKey(k)) {
                        keyKlongs++; keysHere++;
                        if (Klong.getLength(k) == 7) key7++; else keyShort++;
                    } else delKlongs++;
                    Pointee p = ps[i];
                    if (p == null) pNull++;
                    else if (p instanceof Handle) pHandle++;
                    else if (p instanceof ValueNode) {
                        pValue++;
                        valueBytes += ((ValueNode) p).value.length;
                    }
                }
                if (keysHere == 1) {
                    oneKey++;
                    if (kn.isSegmentLeaf()) oneKeyLeaf++;
                    oneKeyArrays += arr;
                }
            } else if (node instanceof TopNode) {
                TopNode tn = (TopNode) node;
                topNodes++;
                topBytes += 64 + align8(12 + 4L * tn.pointers.length)
                        + (16 + 8L * tn.pointersPos.length) + (16 + 8L * tn.pointersTime.length);
            } else other++;
        }
        System.out.println("WALK handles=" + handles + " objects=" + nodes.size() + " keyNodes="
                + keyNodes + " (segment leaves " + leaves + ") topNodes=" + topNodes + " other="
                + other);
        System.out.println("WALK klongs: time=" + timeKlongs + " key=" + keyKlongs
                + " (of 7 bytes, to a segment's tree: " + key7 + "; shorter, to a value: "
                + keyShort + ") other=" + delKlongs);
        System.out.println("WALK pointers of key klongs: handle=" + pHandle + " value=" + pValue
                + " null=" + pNull + "; value bytes " + valueBytes);
        System.out.println("WALK key nodes with exactly one key klong: " + oneKey + " (leaves "
                + oneKeyLeaf + "), their arrays " + oneKeyArrays + " bytes");
        for (java.util.Map.Entry<Integer, long[]> e : byCap.entrySet()) {
            System.out.println(String.format("WALK capacity %3d: %9d key nodes, %10d klongs used,"
                    + " fill %.2f", e.getKey(), e.getValue()[0], e.getValue()[1],
                    e.getValue()[0] == 0 || e.getKey() == 0 ? 0.0
                            : (double) e.getValue()[1] / e.getValue()[0] / e.getKey()));
        }
        System.out.println(String.format("WALK bytes a KV: key node arrays %.1f (one-key nodes'"
                + " %.1f), top nodes %.2f", (double) keyArrays / n, (double) oneKeyArrays / n,
                (double) topBytes / n));
    }
}
