import bergdb.pub.*;
import bergdb.pub.util.LookupTimeNotAvailableException;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.*;

/**
 * Shared code of the 031-08 applications (e1 to e6): the oracle of a Pub database whose
 * values are byte[] at keys with the suffix ".bin", one history per key, and checks of a
 * Connection against it. Written from the Pub API's Javadoc only: a read at lookup time t
 * sees the transactions of time t and earlier (Connection.setLookupTime()); usePrimary()
 * lists a directory's own keys by their names' UTF-8 bytes (UsePrimaryBuilder).
 */
public final class EOracle {
    /** The order of usePrimary(): the names' UTF-8 bytes, unsigned. */
    public static final Comparator<String> ORDER = (a, b) -> Arrays.compareUnsigned(
            a.getBytes(StandardCharsets.UTF_8), b.getBytes(StandardCharsets.UTF_8));

    /** A failure of a check: the application prints FAIL and exits non-zero. */
    public static final class Fail extends RuntimeException {
        public Fail(String m) { super(m); }
    }

    public static void check(boolean ok, String what) {
        if (!ok) throw new Fail(what);
    }

    /** key -> (time -> value, null for a delete). */
    public final HashMap<String, TreeMap<Long, byte[]>> hist = new HashMap<>();
    /** dir -> keys ever written in it. */
    public final HashMap<String, TreeSet<String>> dirs = new HashMap<>();
    /** The times of the application's transactions, in order. */
    public final ArrayList<Long> times = new ArrayList<>();
    public long lastTime = -1;
    /** Each transaction's stored KVs (a delete of an absent key left out, as TransactionInfo.kvs() does). */
    public final HashMap<Long, Map<String, byte[]>> txKvs = new HashMap<>();
    public long liveBytes;   // the bytes of the live values
    public int live;         // the live keys

    public static String dirOf(String k) { return k.substring(0, k.lastIndexOf('/') + 1); }

    /** ops: key -> value, or null for a delete; applied as the transaction of time t. */
    public void apply(Map<String, byte[]> ops, long t) {
        check(t > lastTime, "transaction time " + t + " not after the last, " + lastTime);
        HashMap<String, byte[]> stored = new HashMap<>();
        for (Map.Entry<String, byte[]> e : ops.entrySet()) {
            String k = e.getKey();
            byte[] v = e.getValue();
            byte[] prev = valueAt(k, Long.MAX_VALUE);
            if (prev != null) { liveBytes -= prev.length; live--; }
            if (v != null) { liveBytes += v.length; live++; }
            if (v == null && prev == null) continue;
            stored.put(k, v);
            hist.computeIfAbsent(k, x -> new TreeMap<>()).put(t, v);
            dirs.computeIfAbsent(dirOf(k), x -> new TreeSet<>(ORDER)).add(k);
        }
        txKvs.put(t, stored);
        times.add(t);
        lastTime = t;
    }

    public byte[] valueAt(String k, long t) {
        TreeMap<Long, byte[]> h = hist.get(k);
        if (h == null) return null;
        Map.Entry<Long, byte[]> e = h.floorEntry(t);
        return e == null ? null : e.getValue();
    }

    /** The write time of k's value at t, or -1. */
    public long writeTimeAt(String k, long t) {
        TreeMap<Long, byte[]> h = hist.get(k);
        if (h == null) return -1;
        Map.Entry<Long, byte[]> e = h.floorEntry(t);
        return e == null || e.getValue() == null ? -1 : e.getKey();
    }

    public TreeMap<String, byte[]> dirState(String dir, long t) {
        TreeMap<String, byte[]> m = new TreeMap<>(ORDER);
        TreeSet<String> ks = dirs.get(dir);
        if (ks != null) for (String k : ks) { byte[] v = valueAt(k, t); if (v != null) m.put(k, v); }
        return m;
    }

    /** Forgets versions before t, but each key's version in force at t. */
    public void prune(long t) {
        for (TreeMap<Long, byte[]> h : hist.values()) {
            Long f = h.floorKey(t);
            if (f != null) h.headMap(f, false).clear();
        }
        int i = Collections.binarySearch(times, t);
        int cut = i >= 0 ? i : -i - 1;
        if (cut > 1) times.subList(0, cut - 1).clear();
        txKvs.keySet().removeIf(x -> x < t);
    }

    public List<String> allKeys() {
        ArrayList<String> l = new ArrayList<>(hist.keySet());
        Collections.sort(l);
        return l;
    }

    /**
     * Reads at t through c (whose lookup time this sets): nGets gets of random keys ever
     * written, and a listing of each directory (both ways) whose state at t has at most
     * maxList keys. Returns the reads checked.
     */
    public long verify(Connection c, long t, Random rnd, int nGets, int maxList, String what) {
        c.setLookupTime(t >= Time.MAX.units() ? Time.MAX : Time.units(t));
        long n = 0;
        List<String> ks = allKeys();
        for (int i = 0; i < nGets && !ks.isEmpty(); i++) {
            String k = ks.get(rnd.nextInt(ks.size()));
            byte[] want = valueAt(k, t);
            byte[] got = c.get(k, byte[].class);
            check(Arrays.equals(want, got), what + ": get " + k + " at " + t + ": " + len(got) + " bytes, expected "
                    + len(want) + (got != null && want != null ? " (differ)" : ""));
            n++;
        }
        for (String dir : dirs.keySet()) {
            TreeMap<String, byte[]> st = dirState(dir, t);
            if (st.size() > maxList) continue;
            for (int back = 0; back < 2; back++) {
                UsePrimaryBuilder<byte[]> b = c.usePrimary(byte[].class).dir(dir);
                if (back == 1) b.backward();
                Iterator<Map.Entry<String, byte[]>> want = (back == 0 ? st : st.descendingMap()).entrySet().iterator();
                int idx = 0;
                for (Kv<byte[]> kv : b.kvs()) {
                    check(want.hasNext(), what + ": listing of " + dir + " at " + t + " has an extra key " + kv.key()
                            + " at " + idx + " (expected " + st.size() + ")");
                    Map.Entry<String, byte[]> w = want.next();
                    check(w.getKey().equals(kv.key()), what + ": listing of " + dir + " at " + t + ", index " + idx + ": "
                            + kv.key() + ", expected " + w.getKey());
                    check(Arrays.equals(w.getValue(), kv.value()), what + ": listing of " + dir + " at " + t + ": value of "
                            + kv.key() + " differs");
                    idx++;
                }
                check(!want.hasNext(), what + ": listing of " + dir + " at " + t + " ends at " + idx + ", expected "
                        + st.size());
                n++;
            }
        }
        c.setLookupTime(Time.MAX);
        return n;
    }

    /** A read at t - 1 < first available must be refused (Database.getFirstAvailableLookupTime()). */
    public static void checkExpired(Connection c, long first, String anyKey, String what) {
        if (first <= 0) return;
        c.setLookupTime(Time.units(first - 1));
        try {
            c.get(anyKey, byte[].class);
            throw new Fail(what + ": a get at first available - 1 (" + (first - 1) + ") was not refused");
        } catch (LookupTimeNotAvailableException good) {
        } finally {
            c.setLookupTime(Time.MAX);
        }
    }

    static String len(byte[] b) { return b == null ? "null" : "" + b.length; }

    public static byte[] value(Random r, int len) {
        byte[] v = new byte[len];
        r.nextBytes(v);
        return v;
    }

    public static void rmrf(File f) throws IOException {
        if (!f.exists()) return;
        if (f.isDirectory()) for (File c : Objects.requireNonNull(f.listFiles())) rmrf(c);
        Files.delete(f.toPath());
    }

    public static long dirBytes(File d) {
        long s = 0;
        File[] fs = d.listFiles();
        if (fs != null) for (File f : fs) s += f.isFile() ? f.length() : dirBytes(f);
        return s;
    }

    public static void log(String s) {
        System.out.println(String.format("%tT ", new Date()) + s);
        System.out.flush();
    }

    /** A key of exactly n bytes as stored (bergdb.pub.Limits.keyBytes), n >= dir's bytes + 6, in dir. */
    public static String keyOfBytes(String dir, String tag, int n) {
        String k = dir + tag;
        StringBuilder sb = new StringBuilder(k);
        while (bergdb.pub.Limits.keyBytes(sb.toString() + ".bin") < n) sb.append('x');
        String r = sb + ".bin";
        check(bergdb.pub.Limits.keyBytes(r) == n, "keyOfBytes " + n + ": " + bergdb.pub.Limits.keyBytes(r));
        return r;
    }
}
