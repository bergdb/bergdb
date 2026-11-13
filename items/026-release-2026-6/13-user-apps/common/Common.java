import bergdb.core.Db;
import bergdb.core.Trans;
import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.pub.util.Clock;
import bergdb.pub.util.LookupTimeNotAvailableException;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentSkipListMap;
import java.util.concurrent.atomic.AtomicLong;

/**
 * Shared code of the 024-26 applications: a byte key, the oracle (a versioned in-memory
 * model of the database, one history per key), and checks of a Core Db against it.
 * Written from the Javadoc of Db, Trans.Builder, GetMany, Kvt and GetData only.
 */
public final class Common {
    private Common() {}

    /** A key as bytes, ordered as Arrays.compareUnsigned orders them (Db, "Keys and values"). */
    public static final class K implements Comparable<K> {
        public final byte[] b;
        public K(byte[] b) { this.b = b; }
        @Override public int compareTo(K o) { return Arrays.compareUnsigned(b, o.b); }
        @Override public boolean equals(Object o) { return o instanceof K && Arrays.equals(b, ((K) o).b); }
        @Override public int hashCode() { return Arrays.hashCode(b); }
        @Override public String toString() { return hex(b); }
    }

    public static String hex(byte[] b) {
        if (b == null) return "null";
        StringBuilder sb = new StringBuilder();
        int n = Math.min(b.length, 40);
        for (int i = 0; i < n; i++) sb.append(String.format("%02x", b[i] & 0xff));
        if (b.length > n) sb.append("..(" + b.length + ")");
        return sb.toString();
    }

    /** True for BergDB's own keys, those that start with 01 25 (Db, "Keys and the layers above"). */
    public static boolean isBergKey(byte[] k) {
        return k.length >= 2 && k[0] == 0x01 && k[1] == 0x25;
    }

    /** The sentinel of a delete in a key's history. */
    public static final byte[] DELETED = new byte[0];

    /**
     * The oracle: for each key, its versions by transaction time (DELETED for a delete).
     * Thread-safe for one writer and many readers: the writer adds a transaction's versions
     * with apply() and then publishes its time; readers ask only for published times.
     */
    public static final class Model {
        public final ConcurrentHashMap<K, ConcurrentSkipListMap<Long, byte[]>> hist = new ConcurrentHashMap<>();
        public final TreeMap<K, byte[]> latest = new TreeMap<>();  // writer only
        public final ConcurrentSkipListMap<Long, Integer> times = new ConcurrentSkipListMap<>(); // tt -> ops
        public volatile long lastTime = -1;

        /** ops: key -> value, or DELETED. Applied as the transaction of time tt. */
        public void apply(Map<K, byte[]> ops, long tt) {
            if (tt <= lastTime) throw new Fail("transaction time not increasing: " + tt + " after " + lastTime);
            for (Map.Entry<K, byte[]> e : ops.entrySet()) {
                K k = e.getKey();
                byte[] v = e.getValue();
                byte[] prev = latest.get(k);
                if (v == DELETED) {
                    if (prev == null) continue;          // a delete of an absent key stores nothing
                    latest.remove(k);
                } else {
                    latest.put(k, v);
                }
                hist.computeIfAbsent(k, x -> new ConcurrentSkipListMap<>()).put(tt, v);
            }
            times.put(tt, ops.size());
            lastTime = tt;
        }

        /** The value of k at time t, or null. */
        public byte[] valueAt(K k, long t) {
            ConcurrentSkipListMap<Long, byte[]> h = hist.get(k);
            if (h == null) return null;
            Map.Entry<Long, byte[]> e = h.floorEntry(t);
            if (e == null || e.getValue() == DELETED) return null;
            return e.getValue();
        }

        /** The write time of k's value at time t, or -1. */
        public long writeTimeAt(K k, long t) {
            ConcurrentSkipListMap<Long, byte[]> h = hist.get(k);
            if (h == null) return -1;
            Map.Entry<Long, byte[]> e = h.floorEntry(t);
            if (e == null || e.getValue() == DELETED) return -1;
            return e.getKey();
        }

        /** The state at time t. */
        public TreeMap<K, byte[]> stateAt(long t) {
            TreeMap<K, byte[]> m = new TreeMap<>();
            for (Map.Entry<K, ConcurrentSkipListMap<Long, byte[]>> e : hist.entrySet()) {
                Map.Entry<Long, byte[]> f = e.getValue().floorEntry(t);
                if (f != null && f.getValue() != DELETED) m.put(e.getKey(), f.getValue());
            }
            return m;
        }

        /** Forgets the history before time t, but for each key's version in force at t. */
        public void prune(long t) {
            for (ConcurrentSkipListMap<Long, byte[]> h : hist.values()) {
                Long f = h.floorKey(t);
                if (f != null) h.headMap(f, false).clear();
            }
            hist.entrySet().removeIf(e -> e.getValue().size() == 1 && e.getValue().firstEntry().getValue() == DELETED
                    && e.getValue().firstKey() <= t);
            times.headMap(t, false).clear();
        }

        public int liveCount() { return latest.size(); }
    }

    /** A failure of a check: the application exits non-zero. */
    public static final class Fail extends RuntimeException {
        public Fail(String m) { super(m); }
    }

    public static void check(boolean ok, String what) {
        if (!ok) throw new Fail(what);
    }

    /** Executes the ops in one transaction and applies them to the model. Returns tt. */
    public static long exec(Db db, Model m, Map<K, byte[]> ops) {
        Trans.Builder b = db.trans();
        for (Map.Entry<K, byte[]> e : ops.entrySet()) {
            if (e.getValue() == DELETED) b.delete(e.getKey().b);
            else b.put(e.getKey().b, e.getValue());
        }
        Trans t = b.build();
        db.execute(t);
        m.apply(ops, t.tt);
        return t.tt;
    }

    /** Scans the whole database at lookupTime, BergDB's own keys left out. */
    public static List<Kvt> scanAll(Db db, long lookupTime, long[] actual) {
        GetMany g = db.newGetMany();
        g.lookupTime = lookupTime;
        db.getMany(g);
        if (actual != null) actual[0] = g.actualLookupTime;
        List<Kvt> r = new ArrayList<>(g.result.size());
        for (Kvt kvt : g.result) if (!isBergKey(Keys.toBytes(kvt.key))) r.add(kvt);
        return r;
    }

    /** Compares a scan's KVs with the model's state; also checks Kvt.time's promise. */
    public static void compareScan(String what, List<Kvt> got, Model m, long actual, boolean forward) {
        TreeMap<K, byte[]> exp = m.stateAt(actual);
        Iterator<Map.Entry<K, byte[]>> it = forward ? exp.entrySet().iterator() : exp.descendingMap().entrySet().iterator();
        int i = 0;
        for (Kvt kvt : got) {
            K k = new K(Keys.toBytes(kvt.key));
            if (!it.hasNext()) throw new Fail(what + ": extra KV " + k + " at index " + i + " (expected " + exp.size() + " KVs)");
            Map.Entry<K, byte[]> e = it.next();
            if (!e.getKey().equals(k)) throw new Fail(what + ": index " + i + " got key " + k + ", expected " + e.getKey()
                    + " (got value " + hex(kvt.value) + ", model there " + hex(m.valueAt(k, actual)) + ")");
            if (!Arrays.equals(e.getValue(), kvt.value))
                throw new Fail(what + ": key " + k + " value " + hex(kvt.value) + ", expected " + hex(e.getValue()));
            long wt = m.writeTimeAt(k, actual);
            if (kvt.time < wt || kvt.time > actual)
                throw new Fail(what + ": key " + k + " Kvt.time " + kvt.time + " outside [write " + wt + ", lookup " + actual + "]");
            i++;
        }
        if (it.hasNext()) throw new Fail(what + ": missing KV " + it.next().getKey() + " at index " + i + " (got " + got.size()
                + ", expected " + exp.size() + ")");
    }

    /** Full scan at time t (forward) checked against the model. Returns the count. */
    public static int verifyFull(Db db, Model m, long t, String what) {
        long[] actual = new long[1];
        List<Kvt> got = scanAll(db, t, actual);
        long expActual = Math.min(t, m.lastTime);
        // the actual lookup time is the asked one, or the last transaction's if earlier;
        // BergDB's own transactions may be later than the model's last.
        if (actual[0] < expActual) throw new Fail(what + ": actualLookupTime " + actual[0] + " < " + expActual);
        compareScan(what, got, m, actual[0], true);
        return got.size();
    }

    /** Random gets at time t: present keys, deleted keys and never-written keys. */
    public static void verifyGets(Db db, Model m, long t, Random rnd, int n, String what) {
        GetData gd = db.newGetData();
        List<K> keys = new ArrayList<>(m.hist.keySet());
        if (keys.isEmpty()) return;
        for (int i = 0; i < n; i++) {
            K k;
            if (i % 10 == 9) {
                byte[] b = new byte[1 + rnd.nextInt(12)];
                rnd.nextBytes(b);
                b[0] = (byte) 0xfe;                          // a region no app writes
                k = new K(b);
            } else {
                k = keys.get(rnd.nextInt(keys.size()));
            }
            byte[] got = db.getOne(t, Keys.toSegments(k.b), gd);
            long actual = gd.actualLookupTime;
            byte[] exp = m.valueAt(k, actual);
            if (!Arrays.equals(got, exp))
                throw new Fail(what + ": getOne " + k + " at " + actual + " gave " + hex(got) + ", expected " + hex(exp));
        }
    }

    /** A random range scan, forward or backward, with startKey, endKey or a GetN, checked. */
    public static void verifyRange(Db db, Model m, long t, Random rnd, String what) {
        List<K> keys = new ArrayList<>(m.hist.keySet());
        if (keys.isEmpty()) return;
        K a = keys.get(rnd.nextInt(keys.size()));
        K bk = keys.get(rnd.nextInt(keys.size()));
        if (a.compareTo(bk) > 0) { K x = a; a = bk; bk = x; }
        boolean forward = rnd.nextBoolean();
        boolean inclusive = rnd.nextBoolean();
        GetMany g = db.newGetMany();
        g.lookupTime = t;
        g.forward = forward;
        g.inclusive = inclusive;
        int limit = -1;
        boolean useEnd = false;
        boolean endIncl = true;
        if (forward) {
            g.startKey = Keys.toSegments(a.b);
            if (rnd.nextBoolean()) {
                useEnd = true;
                endIncl = rnd.nextBoolean();
                g.endKey = Keys.toSegments(bk.b);
                g.endInclusive = endIncl;
            } else {
                limit = 1 + rnd.nextInt(200);
                g.stopCondition = new GetMany.GetN(limit);
            }
        } else {
            g.startKey = Keys.toSegments(bk.b);
            limit = 1 + rnd.nextInt(200);
            g.stopCondition = new GetMany.GetN(limit);
        }
        db.getMany(g);
        long actual = g.actualLookupTime;
        TreeMap<K, byte[]> st = m.stateAt(actual);
        NavigableMap<K, byte[]> sub;
        if (forward) {
            sub = st.tailMap(a, inclusive);
            // (the app's own bug, fixed at 22:47: headMap() throws for a key below the tail's start)
            if (useEnd) sub = a.compareTo(bk) == 0 && !(inclusive && endIncl) ? new TreeMap<>() : sub.headMap(bk, endIncl);
        } else {
            sub = st.headMap(bk, inclusive).descendingMap();
        }
        List<Kvt> got = new ArrayList<>();
        int berg = 0;
        for (Kvt kvt : g.result) {
            if (isBergKey(Keys.toBytes(kvt.key))) berg++;   // BergDB's own: lowest, as app keys start at 0x10
            else got.add(kvt);
        }
        if (limit >= 0) limit -= berg;                       // GetN counts every KV, BergDB's own too
        List<Map.Entry<K, byte[]>> exp = new ArrayList<>();
        for (Map.Entry<K, byte[]> e : sub.entrySet()) {
            if (limit >= 0 && exp.size() >= limit) break;
            exp.add(e);
        }
        String desc = what + ": range " + (forward ? "fwd" : "bwd") + " start " + (forward ? a : bk) + (inclusive ? " incl" : " excl")
                + (useEnd ? " end " + bk + (endIncl ? " incl" : " excl") : " limit " + limit);
        if (got.size() != exp.size()) {
            throw new Fail(desc + ": got " + got.size() + " KVs, expected " + exp.size()
                    + firstDiff(got, exp));
        }
        for (int i = 0; i < got.size(); i++) {
            K k = new K(Keys.toBytes(got.get(i).key));
            if (!k.equals(exp.get(i).getKey()) || !Arrays.equals(got.get(i).value, exp.get(i).getValue()))
                throw new Fail(desc + ": index " + i + " got " + k + "=" + hex(got.get(i).value) + ", expected "
                        + exp.get(i).getKey() + "=" + hex(exp.get(i).getValue()));
        }
    }

    /** A prefix scan (GetMany.Prefix or PrefixN) of the first 0 to 9 bytes of a random key, checked. */
    public static void verifyPrefix(Db db, Model m, long t, Random rnd, String what) {
        List<K> keys = new ArrayList<>(m.hist.keySet());
        if (keys.isEmpty()) return;
        K a = keys.get(rnd.nextInt(keys.size()));
        byte[] p = Arrays.copyOf(a.b, Math.min(a.b.length, rnd.nextInt(10)));
        if (p.length == 0) return;
        GetMany g = db.newGetMany();
        g.lookupTime = t;
        g.startKey = Keys.toSegments(p);
        int limit = rnd.nextBoolean() ? -1 : rnd.nextInt(50);
        g.stopCondition = limit < 0 ? new GetMany.Prefix(Keys.toSegments(p)) : new GetMany.PrefixN(Keys.toSegments(p), limit);
        db.getMany(g);
        // BergDB's own keys (01 25 ...) are in a prefix 01 of an app key such as 01 (B1 makes keys under 0x10;
        // soak 2, seed 232, the app's bug): left out, and PrefixN counts them, as verifyRange does for GetN
        List<K> got = new ArrayList<>();
        int berg = 0;
        for (Kvt kvt : g.result) { byte[] k = Keys.toBytes(kvt.key); if (isBergKey(k)) berg++; else got.add(new K(k)); }
        if (limit >= 0) limit -= berg;
        List<K> exp = new ArrayList<>();
        for (Map.Entry<K, byte[]> e : m.stateAt(g.actualLookupTime).tailMap(new K(p), true).entrySet()) {
            byte[] k = e.getKey().b;
            if (k.length < p.length || !Arrays.equals(Arrays.copyOf(k, p.length), p)) break;
            if (limit >= 0 && exp.size() >= limit) break;
            exp.add(e.getKey());
        }
        if (!got.equals(exp)) throw new Fail(what + ": prefix " + hex(p) + (limit >= 0 ? " limit " + limit : "") + " gave "
                + got.size() + " KVs, expected " + exp.size() + (got.isEmpty() || exp.isEmpty() ? "" : "; first " + got.get(0)
                + " / " + exp.get(0)));
    }

    private static String firstDiff(List<Kvt> got, List<Map.Entry<K, byte[]>> exp) {
        int n = Math.min(got.size(), exp.size());
        for (int i = 0; i < n; i++) {
            K k = new K(Keys.toBytes(got.get(i).key));
            if (!k.equals(exp.get(i).getKey())) return "; first difference at " + i + ": got " + k + ", expected " + exp.get(i).getKey();
        }
        return "; lists agree for " + n;
    }

    /** A clock that the application moves: time in clock units (100 ns). */
    public static final class ManualClock implements Clock {
        public final AtomicLong t;
        public ManualClock(long start) { t = new AtomicLong(start); }
        @Override public long getTime() { return t.get(); }
        public void advanceMillis(long ms) { t.addAndGet(ms * 10_000L); }
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

    public static byte[] value(Random rnd, int maxLen) {
        byte[] v = new byte[rnd.nextInt(maxLen + 1)];
        rnd.nextBytes(v);
        return v;
    }

    public static boolean isNotAvailable(Throwable e) {
        for (Throwable c = e; c != null; c = c.getCause()) if (c instanceof LookupTimeNotAvailableException) return true;
        return false;
    }

    public static void log(String s) {
        System.out.println(String.format("%tT ", new Date()) + s);
        System.out.flush();
    }
}
