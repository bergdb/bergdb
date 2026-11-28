import bergdb.pub.*;
import bergdb.pub.util.IndexBuildException;
import bergdb.pub.util.Job;
import bergdb.pub.util.JobStatus;
import bergdb.pub.util.LookupTimeNotAvailableException;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.util.*;

/**
 * App e3 of 031-08: user indexes created, built while the application writes, deleted and
 * created again, with maintain(budget) calls, reclaim and restarts in between (Pub API, a
 * file database, a test clock that the app moves).
 *
 * Objects of one Data Object class (a long n, a long g, a String s that is absent in a
 * tenth, a double d with -0.0, 0.0 and the infinities, a byte[] b) in two directories. Five
 * index definitions (by n; by g then n; by s; by d; by b), of which up to four exist at a
 * time under the names ix0 to ix3, each name taking a new definition when it is made again.
 * Rounds of: w() transactions of 1 to 150 puts and deletes (overwrites of objects, Strings put
 * over objects, deletes), an index started (start(), then writes while it builds, then join()),
 * deleted, or deleted and made again under its name with another definition, maintain()
 * calls, the clock moved by 0 to R/3, restarts (also while a build runs: the next start takes
 * it again). After each round, scans of every active index against the oracle (each
 * object's levels by IndexBuilder's rules: a level of the wrong kind or an absent field gives
 * no entry; the order of the levels, then the keys' names by UTF-8): the whole index both
 * ways, from() and to() bounds, eq() on the first level, prefix() of a string level; at the
 * latest time and at an older time inside the retain duration, where the definition is the
 * one in force then (a deleted index still scans at a time when it was active, until reclaim's
 * cut passes it); a scan of a name at a time when it did not exist, or was building, throws
 * NoSuchIndexException. Gets and both listings of each directory, at the latest and older
 * times, against the oracle.
 *
 * Usage: java E3IndexReclaim SEED DIR [ROUNDS]
 */
public class E3IndexReclaim {
    public static class Item {
        public long n;
        public long g;
        public String s;
        public double d;
        public byte[] b;
        public Item() {}
    }

    static final long T0 = Time.utc("2026-03-01").units();
    static final long SEC = 10_000_000L;
    static final String[] DIRS = {"/e3/items/", "/e3/more/"};
    // the definitions: dir index, then levels (type, field)
    static final String[][][] DEFS = {
            {{"0"}, {"long", "n"}},
            {{"0"}, {"long", "g"}, {"long", "n"}},
            {{"0"}, {"string", "s"}},
            {{"1"}, {"double", "d"}},
            {{"1"}, {"bytes", "b"}, {"long", "g"}},
    };

    /** An index name's history: from a time, its definition (or -1 none, or building). */
    static final class Era { long from; int def; boolean active; Era(long f, int d, boolean a) { from = f; def = d; active = a; } }

    final long seed;
    final Random rnd;
    final File dir;
    final TestClock clock = new TestClock();
    final long retain;
    // key -> time -> Item (null: deleted; a String put over an object is kept as STRING)
    final HashMap<String, TreeMap<Long, Object>> hist = new HashMap<>();
    final HashMap<String, List<Era>> eras = new HashMap<>();
    final ArrayList<Long> times = new ArrayList<>();
    static final Object DELETED = new Object();
    Database db;
    Connection c;
    long lastFirst, scans, txs, builds, deletes, maintains, restarts, refusedScans, deletedWhileBuilding, buildDoneBeforeDelete;
    final Map<String, Job> running = new HashMap<>();
    final Map<String, Integer> runningDef = new HashMap<>();

    E3IndexReclaim(long seed, File dir) {
        this.seed = seed;
        rnd = new Random(seed);
        this.dir = dir;
        retain = new long[] {SEC, 5 * SEC, 30 * SEC}[rnd.nextInt(3)];
    }

    void start(boolean create) {
        db = (create ? Factory.database().create(dir.getPath()) : Factory.database().open(dir.getPath())).clock(clock).cacheSizeInMb(64).start();
        c = db.connection();
    }

    void tick(long u) { clock.setTime(Time.units(clock.getTime() + u)); }

    long now() { return db.currentTime().units(); }

    Item item() {
        Item it = new Item();
        it.n = rnd.nextInt(400) - 100;
        it.g = rnd.nextInt(6);
        int x = rnd.nextInt(10);
        it.s = x == 0 ? null : str(rnd.nextInt(8));
        double[] ds = {0.0, -0.0, Double.POSITIVE_INFINITY, Double.NEGATIVE_INFINITY, 1.5, -2.25};
        it.d = rnd.nextInt(5) == 0 ? ds[rnd.nextInt(ds.length)] : (rnd.nextInt(2000) - 1000) / 8.0;
        it.b = new byte[rnd.nextInt(5)];
        for (int i = 0; i < it.b.length; i++) it.b[i] = (byte) new int[] {0, 1, 2, 0x7f, 0x80, 0xff}[rnd.nextInt(6)];
        return it;
    }

    String str(int len) {
        String alpha = "abå中\u0000\u0001z";
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < len; i++) sb.append(alpha.charAt(rnd.nextInt(alpha.length())));
        return sb.toString();
    }

    Object at(String k, long t) {
        TreeMap<Long, Object> h = hist.get(k);
        if (h == null) return null;
        Map.Entry<Long, Object> e = h.floorEntry(t);
        return e == null || e.getValue() == DELETED ? null : e.getValue();
    }

    void apply(Map<String, Object> ops, long t) {
        for (Map.Entry<String, Object> e : ops.entrySet())
            hist.computeIfAbsent(e.getKey(), x -> new TreeMap<>()).put(t, e.getValue() == null ? DELETED : e.getValue());
        times.add(t);
        txs++;
    }

    void writes(Connection cn, int n) {
        LinkedHashMap<String, Object> ops = new LinkedHashMap<>();
        WBuilder w = cn.w();
        for (int j = 0; j < n; j++) {
            String k = DIRS[rnd.nextInt(2)] + "k" + rnd.nextInt(600);
            int x = rnd.nextInt(10);
            if (x < 2) { w.delete(k); ops.put(k, null); }
            else if (x < 3) { String v = "text" + rnd.nextInt(); w.put(k, v); ops.put(k, v); }
            else { Item it = item(); w.put(k, it); ops.put(k, it); }
        }
        apply(ops, w.execute().getTime().units());
    }

    /** The levels of v for the definition, or null for no entry (IndexBuilder's rules). */
    static Object[] levels(Object v, int def) {
        if (!(v instanceof Item)) return null;
        Item it = (Item) v;
        String[][] d = DEFS[def];
        Object[] l = new Object[d.length - 1];
        for (int i = 1; i < d.length; i++) {
            switch (d[i][1]) {
                case "n": l[i - 1] = it.n; break;
                case "g": l[i - 1] = it.g; break;
                case "s": if (it.s == null) return null; l[i - 1] = it.s; break;
                case "d": l[i - 1] = it.d == 0.0 ? 0.0 : it.d; break;
                case "b": l[i - 1] = it.b; break;
            }
        }
        return l;
    }

    static int cmpLevel(Object a, Object b) {
        if (a instanceof Long) return Long.compare((Long) a, (Long) b);
        if (a instanceof Double) return Double.compare((Double) a, (Double) b);
        if (a instanceof String) {
            String x = (String) a, y = (String) b;
            int[] p = x.codePoints().toArray(), q = y.codePoints().toArray();
            return Arrays.compare(p, q);
        }
        return Arrays.compareUnsigned((byte[]) a, (byte[]) b);
    }

    static int cmpLevels(Object[] a, Object[] b) {
        for (int i = 0; i < a.length; i++) { int c = cmpLevel(a[i], b[i]); if (c != 0) return c; }
        return 0;
    }

    static int cmpName(String a, String b) {
        return Arrays.compareUnsigned(a.getBytes(StandardCharsets.UTF_8), b.getBytes(StandardCharsets.UTF_8));
    }

    /**
     * The definition of the name at t: -1 for none, -2 while it may be building or active
     * (from start() until join() returned: the build's last step has a time in between).
     */
    int defAt(String name, long t) {
        List<Era> es = eras.get(name);
        if (es == null) return -1;
        Era found = null;
        for (Era e : es) if (e.from <= t) found = e;
        if (found == null || found.def < 0) return -1;
        return found.active ? found.def : -2;
    }

    /** The expected scan: keys of the def's dir with an entry, filtered and ordered. */
    List<String> expected(int def, long t, Object lo, boolean loIncl, Object hi, boolean hiIncl, Object eq0, String prefix, boolean back) {
        String d = DIRS[Integer.parseInt(DEFS[def][0][0])];
        List<Object[]> rows = new ArrayList<>();
        for (String k : hist.keySet()) {
            if (!k.substring(0, k.lastIndexOf('/') + 1).equals(d)) continue;
            Object v = at(k, t);
            Object[] l = levels(v, def);
            if (l == null) continue;
            int bl = 0;
            if (eq0 != null) { if (cmpLevel(l[0], eq0) != 0) continue; bl = 1; }
            if (lo != null) { int cc = cmpLevel(l[bl], lo); if (cc < 0 || (cc == 0 && !loIncl)) continue; }
            if (hi != null) { int cc = cmpLevel(l[bl], hi); if (cc > 0 || (cc == 0 && !hiIncl)) continue; }
            if (prefix != null && !((String) l[bl]).startsWith(prefix)) continue;
            rows.add(new Object[] {l, k});
        }
        rows.sort((x, y) -> { int cc = cmpLevels((Object[]) x[0], (Object[]) y[0]); return cc != 0 ? cc : cmpName(((String) x[1]).substring(d.length()), ((String) y[1]).substring(d.length())); });
        List<String> out = new ArrayList<>();
        for (Object[] r : rows) out.add((String) r[1]);
        if (back) Collections.reverse(out);
        return out;
    }

    void scanIndexes(long t, String what) {
        Connection cn = db.newConnection();
        cn.setLookupTime(Time.units(t));
        for (String name : new String[] {"ix0", "ix1", "ix2", "ix3"}) {
            int def = defAt(name, t);
            if (def == -2) continue;
            if (def < 0) {
                try {
                    cn.useIndex(name, Item.class);
                    throw new EOracle.Fail(what + ": useIndex(" + name + ") at " + t + " was taken, the index is absent or building then");
                } catch (NoSuchIndexException good) {
                    refusedScans++;
                }
                continue;
            }
            for (int q = 0; q < 3; q++) {
                UseIndexBuilder<Item> b = cn.useIndex(name, Item.class);
                Object lo = null, hi = null, eq0 = null;
                boolean loI = rnd.nextBoolean(), hiI = rnd.nextBoolean(), back = rnd.nextBoolean();
                String prefix = null;
                String[][] d = DEFS[def];
                int lvl = 1;
                if (q > 0 && d.length > 2 && rnd.nextBoolean()) {
                    Object v = sample(d[1][0]);
                    eq0 = v;
                    eqCall(b, d[1][0], v);
                    lvl = 2;
                }
                if (q > 0) {
                    String type = d[lvl][0];
                    if (type.equals("string") && rnd.nextBoolean()) { prefix = str(rnd.nextInt(3)); b.prefix(prefix); }
                    else {
                        if (rnd.nextBoolean()) { lo = sample(type); fromCall(b, type, lo, loI); }
                        if (rnd.nextBoolean()) { hi = sample(type); toCall(b, type, hi, hiI); }
                    }
                }
                if (back) b.backward();
                List<String> want = expected(def, t, lo, loI, hi, hiI, eq0, prefix, back);
                List<String> got = new ArrayList<>();
                for (Kv<Item> kv : b.kvs()) {
                    got.add(kv.key());
                    Object v = at(kv.key(), t);
                    EOracle.check(v instanceof Item && ((Item) v).n == kv.value().n && ((Item) v).g == kv.value().g
                            && Objects.equals(((Item) v).s, kv.value().s) && Arrays.equals(((Item) v).b, kv.value().b),
                            what + ": index " + name + " gives a value at " + kv.key() + " that differs from the oracle's");
                }
                EOracle.check(got.equals(want), what + ": index " + name + " (definition " + def + ") at " + t + " query " + q
                        + " eq " + eq0 + " from " + str(lo) + (loI ? "" : " excl") + " to " + str(hi) + (hiI ? "" : " excl") + " prefix " + prefix
                        + (back ? " backward" : "") + ": got " + got.size() + " " + head(got) + ", expected " + want.size() + " " + head(want));
                scans++;
            }
        }
    }

    static String str(Object o) { return o instanceof byte[] ? Arrays.toString((byte[]) o) : String.valueOf(o); }

    static String head(List<String> l) { return l.subList(0, Math.min(4, l.size())).toString(); }

    Object sample(String type) {
        switch (type) {
            case "long": return (long) (rnd.nextInt(420) - 110);
            case "double": return (rnd.nextInt(2000) - 1000) / 8.0;
            case "string": return str(rnd.nextInt(4));
            default: { byte[] b = new byte[rnd.nextInt(3)]; for (int i = 0; i < b.length; i++) b[i] = (byte) new int[] {0, 1, 0x80, 0xff}[rnd.nextInt(4)]; return b; }
        }
    }

    static void eqCall(UseIndexBuilder<Item> b, String type, Object v) {
        switch (type) { case "long": b.eq((Long) v); break; case "double": b.eq((Double) v); break; case "string": b.eq((String) v); break; default: b.eq((byte[]) v); }
    }

    static void fromCall(UseIndexBuilder<Item> b, String type, Object v, boolean incl) {
        switch (type) { case "long": b.from((Long) v, incl); break; case "double": b.from((Double) v, incl); break; case "string": b.from((String) v, incl); break; default: b.from((byte[]) v, incl); }
    }

    static void toCall(UseIndexBuilder<Item> b, String type, Object v, boolean incl) {
        switch (type) { case "long": b.to((Long) v, incl); break; case "double": b.to((Double) v, incl); break; case "string": b.to((String) v, incl); break; default: b.to((byte[]) v, incl); }
    }

    void startIndex(String name, int def) {
        IndexBuilder ib = db.indexBuilder(name).dir(DIRS[Integer.parseInt(DEFS[def][0][0])]);
        for (int i = 1; i < DEFS[def].length; i++) ib.type(DEFS[def][i][0]).field(DEFS[def][i][1]);
        Job j = ib.start();
        long t = now();
        eras.computeIfAbsent(name, x -> new ArrayList<>()).add(new Era(t, def, false));
        running.put(name, j);
        runningDef.put(name, def);
        builds++;
    }

    void joinAll(String what) {
        for (Map.Entry<String, Job> e : new ArrayList<>(running.entrySet())) {
            JobStatus st = e.getValue().join();
            EOracle.check(st.state() == JobStatus.State.ACTIVE, what + ": the build of " + e.getKey() + " ended " + st.state());
            long t = now();
            eras.get(e.getKey()).add(new Era(t, runningDef.get(e.getKey()), true));
        }
        running.clear();
        runningDef.clear();
    }

    void checkAll(String what) {
        long first = db.getFirstAvailableLookupTime().units();
        EOracle.check(first >= lastFirst, what + ": the first available time moved back");
        lastFirst = first;
        long n = now();
        EOracle.check(first <= n - retain, what + ": first available after now - R");
        scanIndexes(n, what + " latest");
        long lo = Math.max(first, n - retain);
        int i = Collections.binarySearch(times, lo);
        int from = i >= 0 ? i : -i - 1;
        if (from < times.size()) {
            long t = times.get(from + rnd.nextInt(times.size() - from));
            scanIndexes(t, what + " older");
            if (t - 1 >= lo) scanIndexes(t - 1, what + " older - 1");
        }
        // gets and listings
        Connection cn = db.newConnection();
        for (long t : new long[] {n, lo}) {
            cn.setLookupTime(Time.units(t));
            for (String d : DIRS) {
                TreeMap<String, Object> st = new TreeMap<>(EOracle.ORDER);
                for (String k : hist.keySet()) if (k.startsWith(d) && at(k, t) != null) st.put(k, at(k, t));
                Iterator<Map.Entry<String, Object>> it = st.entrySet().iterator();
                for (Kv<Object> kv : cn.usePrimary(Object.class).dir(d).kvs()) {
                    EOracle.check(it.hasNext(), what + ": listing of " + d + " at " + t + " has an extra " + kv.key());
                    Map.Entry<String, Object> e = it.next();
                    EOracle.check(e.getKey().equals(kv.key()), what + ": listing of " + d + " at " + t + ": " + kv.key() + ", expected " + e.getKey());
                    // a String at an object key reads as its bytes through Object.class (Connection.get())
                    if (e.getValue() instanceof String) EOracle.check(kv.value() instanceof byte[] && Arrays.equals(((String) e.getValue())
                            .getBytes(StandardCharsets.UTF_8), (byte[]) kv.value()), what + ": the String at " + kv.key() + " differs");
                    else EOracle.check(kv.value() instanceof DbObject, what + ": the object at " + kv.key() + " is read as " + kv.value().getClass());
                }
                EOracle.check(!it.hasNext(), what + ": listing of " + d + " at " + t + " lacks " + (it.hasNext() ? it.next().getKey() : ""));
            }
        }
    }

    void restart(String what) {
        long first = db.getFirstAvailableLookupTime().units();
        if (rnd.nextBoolean()) db.close(); else { db.stop(); db.close(); }
        start(false);
        restarts++;
        EOracle.check(db.getFirstAvailableLookupTime().units() == first, what + ": the restart changed the first available time");
        // builds that ran are taken again by the start
        for (String name : new ArrayList<>(running.keySet())) running.put(name, db.indexJob(name));
    }

    void run(int rounds) throws Exception {
        EOracle.log("E3IndexReclaim seed " + seed + ", R " + retain / SEC + " s, rounds " + rounds);
        EOracle.rmrf(dir);
        clock.setTime(Time.units(T0));
        start(true);
        db.setStartupDistanceInMb(5);
        db.setRetainDuration(Duration.units(retain));
        for (int j = 0; j < 10; j++) { writes(c, 50); tick(rnd.nextInt(100_000)); }
        startIndex("ix0", 0);
        joinAll("first build");
        checkAll("first build");
        for (int round = 0; round < rounds; round++) {
            tick((long) (rnd.nextDouble() * retain / 3));
            int a = rnd.nextInt(20);
            String name = "ix" + rnd.nextInt(4);
            if (a < 10) writes(c, 1 + rnd.nextInt(50));
            else if (a < 13 && !running.containsKey(name)) {
                List<Era> es = eras.get(name);
                boolean exists = es != null && !es.isEmpty() && es.get(es.size() - 1).def >= 0;
                if (exists) {
                    db.deleteIndex(name);
                    long t = now();
                    eras.get(name).add(new Era(t, -1, false));
                    deletes++;
                }
                if (!exists || rnd.nextBoolean()) {
                    int def = rnd.nextInt(DEFS.length);
                    startIndex(name, def);
                    // writes while it builds
                    for (int j = 0; j < 1 + rnd.nextInt(6); j++) {
                        writes(c, 1 + rnd.nextInt(50));
                        tick(rnd.nextInt(200_000));
                        if (rnd.nextInt(3) == 0) { db.maintain(new int[] {100, 100_000}[rnd.nextInt(2)]); maintains++; }
                    }
                    if (rnd.nextInt(4) == 0) restart("round " + round + ", during a build");
                    if (rnd.nextInt(8) == 0) {
                        // deleted while it builds: its join() throws IndexBuildException, FAILED (IndexBuilder.start())
                        Job j = running.remove(name);
                        runningDef.remove(name);
                        db.deleteIndex(name);
                        long t = now();
                        eras.get(name).add(new Era(t, -1, false));
                        deletes++;
                        try {
                            JobStatus st = j.join();
                            // the build may have ended before the deletion
                            EOracle.check(st.state() == JobStatus.State.ACTIVE, "round " + round + ": a build deleted ended " + st.state());
                            buildDoneBeforeDelete++;
                        } catch (IndexBuildException e) {
                            EOracle.check(e.getStatus().state() == JobStatus.State.FAILED, "round " + round + ": the deleted build's status " + e.getStatus().state());
                            deletedWhileBuilding++;
                        }
                    }
                    joinAll("round " + round);
                }
            } else if (a < 16) {
                int n = 1 + rnd.nextInt(8);
                for (int j = 0; j < n; j++) { db.maintain(new int[] {0, 100, 5000, 100_000}[rnd.nextInt(4)]); maintains++; tick(rnd.nextInt((int) (retain / 8))); }
            } else if (a < 17) {
                restart("round " + round);
                joinAll("round " + round + " after a restart");
            } else {
                writes(c, 1 + rnd.nextInt(20));
            }
            if (round % 3 == 0) checkAll("round " + round);
            if (round % 100 == 99) EOracle.log("  round " + round + ": stream " + db.getStreamSize() + ", builds " + builds + ", deletes " + deletes
                    + ", scans " + scans + ", first " + db.getFirstAvailableLookupTime().units());
        }
        joinAll("end");
        checkAll("end");
        restart("end");
        joinAll("end, restarted");
        checkAll("end, restarted");
        db.close();
        EOracle.log("OK E3IndexReclaim seed " + seed + ": " + txs + " transactions, " + builds + " builds, " + deletes + " deletions, "
                + maintains + " maintain calls, " + restarts + " restarts, " + scans + " index scans checked, " + refusedScans
                + " refused as absent or building, " + deletedWhileBuilding + " builds deleted while building (" + buildDoneBeforeDelete + " done before)");
        EOracle.rmrf(dir);
    }

    public static void main(String[] a) throws Exception {
        long seed = Long.parseLong(a[0]);
        File dir = new File(a[1]);
        int rounds = a.length > 2 ? Integer.parseInt(a[2]) : 600;
        E3IndexReclaim app = new E3IndexReclaim(seed, dir);
        try {
            app.run(rounds);
        } catch (Throwable t) {
            System.out.println("FAIL E3IndexReclaim seed " + seed + ": " + t);
            t.printStackTrace(System.out);
            try { if (app.db != null) app.db.close(); } catch (Throwable x) { }
            System.exit(1);
        }
    }
}
