import bergdb.pub.*;
import bergdb.pub.util.LookupTimeNotAvailableException;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.util.*;

/**
 * App 6 of 024-26: Pub API objects with two user indexes under delete-heavy churn, with
 * long keys and long index levels (BergDB's own index entries are its keys longer than
 * 111 bytes, which the Core's merges and dead-klong compactions now handle too), reclaim
 * with a short retain duration on a clock that the application moves, restarts, and reads
 * at older times. The oracle is every key's history; each check compares the primary scan,
 * gets, and index scans (full, eq, bounds, prefix, backward) with it.
 *
 * Usage: java -cp bergdb-release.jar:out IndexChurn SEED TRANSACTIONS DIR [retainMs] [keys]
 */
public class IndexChurn {
    public static class Item {
        public String name;
        public long n;
        public String note;
        public Item() {}
        public Item(String name, long n, String note) { this.name = name; this.n = n; this.note = note; }
        @Override public boolean equals(Object o) {
            if (!(o instanceof Item)) return false;
            Item x = (Item) o;
            return Objects.equals(name, x.name) && n == x.n && Objects.equals(note, x.note);
        }
        @Override public String toString() { return "Item(" + name + ", " + n + ")"; }
    }

    static final Comparator<String> UTF8 = (a, b) -> Arrays.compareUnsigned(a.getBytes(StandardCharsets.UTF_8),
            b.getBytes(StandardCharsets.UTF_8));
    static final String DIR = "/items/";

    static Random rnd;
    static File dir;
    static Database db;
    static Connection c;
    static Common.ManualClock clock;
    /** key -> (time -> Item, or null for a delete) */
    static final TreeMap<String, TreeMap<Long, Item>> hist = new TreeMap<>(UTF8);
    static final TreeMap<String, Item> latest = new TreeMap<>(UTF8);
    static final List<Long> times = new ArrayList<>();
    static final List<String> keyPool = new ArrayList<>();
    static long txCount, restarts, checks, oldOk, oldCut;
    static long retain;

    public static void main(String[] a) throws Exception {
        long seed = Long.parseLong(a[0]);
        long nTx = Long.parseLong(a[1]);
        dir = new File(a[2]);
        long retainMs = a.length > 3 ? Long.parseLong(a[3]) : 1000;
        int nKeys = a.length > 4 ? Integer.parseInt(a[4]) : 1500;
        retain = retainMs * 10_000L;
        rnd = new Random(seed);
        Common.rmrf(dir);
        clock = new Common.ManualClock(1_778_000_000_000L * 10_000L);
        for (int i = 0; i < nKeys; i++) keyPool.add(makeKey(i));
        long t0 = System.currentTimeMillis();
        try {
            open(true);
            db.indexBuilder("byname").dir(DIR).type("string").field("name").start().join();
            db.indexBuilder("bynamen").dir(DIR).type("string").field("name").type("long").field("n").start().join();
            if (retainMs > 0) db.setRetainDuration(Duration.units(retain));
            long nextRestart = 100 + rnd.nextInt(300);
            for (long i = 0; i < nTx; i++) {
                clock.advanceMillis(rnd.nextInt(30));
                transaction(i);
                if (i % 40 == 39) verify("tx " + i);
                if (i == nextRestart) {
                    db.close();
                    open(false);
                    restarts++;
                    verify("tx " + i + " after restart");
                    nextRestart = i + 100 + rnd.nextInt(400);
                }
                if (i % 1000 == 999) Common.log("tx " + i + ": live " + latest.size() + ", restarts " + restarts + ", checks "
                        + checks + ", old ok " + oldOk + ", cut " + oldCut + ", first available "
                        + db.getFirstAvailableLookupTime().units());
            }
            db.close();
            open(false);
            verify("final");
            db.close();
        } catch (Common.Fail f) {
            System.out.println("FAIL IndexChurn seed " + seed + ": " + f.getMessage());
            System.out.println("  after " + txCount + " transactions, " + restarts + " restarts");
            try { db.close(); } catch (Throwable t) { }
            System.exit(1);
        } catch (Throwable t) {
            System.out.println("FAIL (exception) IndexChurn seed " + seed + ": " + t);
            t.printStackTrace(System.out);
            System.out.println("  after " + txCount + " transactions, " + restarts + " restarts");
            try { db.close(); } catch (Throwable x) { }
            System.exit(2);
        }
        Common.log("OK IndexChurn seed " + seed + ": " + txCount + " transactions, " + restarts + " restarts, " + checks
                + " checks, old reads " + oldOk + " ok and " + oldCut + " cut, live " + latest.size() + ", "
                + (System.currentTimeMillis() - t0) + " ms");
    }

    static void open(boolean create) {
        DatabaseBuilder b = Factory.database().clock(clock).cacheSizeInMb(8);
        db = (create ? b.create(dir.getPath()) : b.open(dir.getPath())).start();
        db.setStartupDistanceInMb(1);       // after the start since bergdb 028-13 (5 MB, clamped)
        c = db.connection();
    }

    static final String[] PIECES = {"a", "b", "å", "€", "😀", "z", "-", "."};

    /** An object key of up to 111 bytes as stored, many sharing long starts. */
    static String makeKey(int i) {
        StringBuilder sb = new StringBuilder(DIR);
        int shape = i % 4;
        if (shape == 0) sb.append("k").append(i);
        else if (shape == 1) sb.append("shared-prefix-of-some-length-").append(i % 7).append('-').append(i);
        else {
            sb.append(shape == 2 ? "long-" : "läng-€-");
            Random r = new Random(i);
            int target = 60 + r.nextInt(52);
            while (true) {
                String p = PIECES[r.nextInt(PIECES.length - 1)];   // no '.': it would make a suffix
                if (stored(sb + p + i) > target) break;
                sb.append(p);
            }
            sb.append(i);
        }
        String k = sb.toString();
        if (stored(k) > 111) throw new IllegalStateException("key too long: " + k);
        return k;
    }

    static int stored(String key) {
        int slashes = 0;
        for (char ch : key.toCharArray()) if (ch == '/') slashes++;
        return key.getBytes(StandardCharsets.UTF_8).length + slashes;
    }

    /** A name whose level (UTF-8 + 1) is at most 102 + 1 bytes, so that name + n fits 111. */
    static String makeName() {
        int kind = rnd.nextInt(5);
        if (kind == 0) return "n" + rnd.nextInt(30);
        StringBuilder sb = new StringBuilder(kind == 1 ? "common-prefix-" : kind == 2 ? "Ünïcödé-€-" : "");
        int target = rnd.nextInt(103);
        while (true) {
            String p = PIECES[rnd.nextInt(PIECES.length)];
            if ((sb + p).getBytes(StandardCharsets.UTF_8).length > target) break;
            sb.append(p);
        }
        return sb.toString();
    }

    static void transaction(long i) {
        int n = 1 + rnd.nextInt(rnd.nextInt(10) == 0 ? 90 : 15);
        LinkedHashMap<String, Item> ops = new LinkedHashMap<>();
        int mode = (int) ((i / 300) % 3);   // 0 fill, 1 delete-heavy, 2 mixed
        int hot = rnd.nextInt(keyPool.size());
        for (int j = 0; j < n; j++) {
            String k;
            if (rnd.nextBoolean()) k = keyPool.get((hot + rnd.nextInt(50)) % keyPool.size());
            else k = keyPool.get(rnd.nextInt(keyPool.size()));
            boolean del = mode == 0 ? rnd.nextInt(10) == 0 : mode == 1 ? rnd.nextInt(10) < 8 : rnd.nextInt(3) == 0;
            Item v = null;
            if (!del) {
                Item old = latest.get(k);
                if (old != null && rnd.nextBoolean()) v = new Item(old.name, old.n, "note" + i);     // same levels
                else v = new Item(makeName(), rnd.nextInt(1000) - 500, rnd.nextInt(4) == 0 ? null : "t" + i);
            }
            ops.remove(k);
            ops.put(k, v);
        }
        Transaction t;
        if (rnd.nextInt(4) == 0) {
            t = c.rw(env -> {
                for (Map.Entry<String, Item> e : ops.entrySet()) {
                    if (e.getValue() == null) env.delete(e.getKey());
                    else env.put(e.getKey(), e.getValue());
                }
            });
        } else {
            WBuilder w = c.w();
            for (Map.Entry<String, Item> e : ops.entrySet()) {
                if (e.getValue() == null) w.delete(e.getKey());
                else w.put(e.getKey(), e.getValue());
            }
            t = w.execute();
        }
        long tt = t.getTime().units();
        for (Map.Entry<String, Item> e : ops.entrySet()) {
            if (e.getValue() == null && !latest.containsKey(e.getKey())) continue;
            hist.computeIfAbsent(e.getKey(), x -> new TreeMap<>()).put(tt, e.getValue());
            if (e.getValue() == null) latest.remove(e.getKey());
            else latest.put(e.getKey(), e.getValue());
        }
        times.add(tt);
        txCount++;
    }

    static TreeMap<String, Item> stateAt(long t) {
        TreeMap<String, Item> m = new TreeMap<>(UTF8);
        for (Map.Entry<String, TreeMap<Long, Item>> e : hist.entrySet()) {
            Map.Entry<Long, Item> f = e.getValue().floorEntry(t);
            if (f != null && f.getValue() != null) m.put(e.getKey(), f.getValue());
        }
        return m;
    }

    static void verify(String what) {
        verifyAt(c, latest, what + " latest");
        // Old states: inside the retain duration they must be readable.
        long now = db.currentTime().units();
        for (int i = 0; i < 2 && !times.isEmpty(); i++) {
            long t = times.get(rnd.nextInt(times.size()));
            if (rnd.nextBoolean()) t--;
            Connection oc = db.newConnection();
            oc.setLookupTime(Time.units(t));
            try {
                verifyAt(oc, stateAt(t), what + " at " + t);
                oldOk++;
            } catch (LookupTimeNotAvailableException e) {
                long fa = db.getFirstAvailableLookupTime().units();
                if (retain == 0 || t >= now - retain) throw new Common.Fail(what + ": read at " + t + " cut inside the retain duration");
                if (fa <= t) throw new Common.Fail(what + ": read at " + t + " cut, first available " + fa);
                oldCut++;
            }
        }
        // Forget the history before the first available time.
        long fa = db.getFirstAvailableLookupTime().units();
        times.removeIf(x -> x < fa);
    }

    static void verifyAt(Connection cn, TreeMap<String, Item> exp, String what) {
        // The primary scan.
        List<String> got = new ArrayList<>();
        for (Kv<Item> kv : cn.usePrimary(Item.class).dir(DIR).kvs()) {
            Item e = exp.get(kv.key());
            if (!kv.value().equals(e)) throw new Common.Fail(what + ": primary " + kv.key() + " = " + kv.value() + ", expected " + e);
            got.add(kv.key());
        }
        if (!got.equals(new ArrayList<>(exp.keySet())))
            throw new Common.Fail(what + ": primary lists " + got.size() + " keys, expected " + exp.size());
        checks++;
        // Gets.
        for (int i = 0; i < 20; i++) {
            String k = keyPool.get(rnd.nextInt(keyPool.size()));
            Item g = cn.get(k, Item.class);
            if (!Objects.equals(g, exp.get(k))) throw new Common.Fail(what + ": get " + k + " = " + g + ", expected " + exp.get(k));
            checks++;
        }
        // byname: all, eq, from/to, prefix, backward.
        List<Map.Entry<String, Item>> byName = new ArrayList<>(exp.entrySet());
        byName.sort((x, y) -> {
            int r = UTF8.compare(x.getValue().name, y.getValue().name);
            return r != 0 ? r : UTF8.compare(x.getKey(), y.getKey());
        });
        compare(cn.useIndex("byname", Item.class).kvs(), byName, what + " byname");
        List<Map.Entry<String, Item>> rev = new ArrayList<>(byName);
        Collections.reverse(rev);
        compare(cn.useIndex("byname", Item.class).backward().kvs(), rev, what + " byname backward");
        if (!byName.isEmpty()) {
            String nm = byName.get(rnd.nextInt(byName.size())).getValue().name;
            List<Map.Entry<String, Item>> eq = new ArrayList<>();
            for (Map.Entry<String, Item> e : byName) if (e.getValue().name.equals(nm)) eq.add(e);
            compare(cn.useIndex("byname", Item.class).eq(nm).kvs(), eq, what + " byname eq");
            String lo = byName.get(rnd.nextInt(byName.size())).getValue().name;
            String hi = byName.get(rnd.nextInt(byName.size())).getValue().name;
            boolean li = rnd.nextBoolean(), hiIncl = rnd.nextBoolean();
            List<Map.Entry<String, Item>> rg = new ArrayList<>();
            for (Map.Entry<String, Item> e : byName) {
                int a = UTF8.compare(e.getValue().name, lo), b = UTF8.compare(e.getValue().name, hi);
                if ((li ? a >= 0 : a > 0) && (hiIncl ? b <= 0 : b < 0)) rg.add(e);
            }
            compare(cn.useIndex("byname", Item.class).from(lo, li).to(hi, hiIncl).kvs(), rg, what + " byname range");
            String pre = nm.length() > 3 ? nm.substring(0, nm.offsetByCodePoints(0, Math.min(3, nm.codePointCount(0, nm.length())))) : nm;
            List<Map.Entry<String, Item>> pr = new ArrayList<>();
            for (Map.Entry<String, Item> e : byName) if (e.getValue().name.startsWith(pre)) pr.add(e);
            compare(cn.useIndex("byname", Item.class).prefix(pre).kvs(), pr, what + " byname prefix " + pre);
            // bynamen: eq(name), then n's order.
            List<Map.Entry<String, Item>> en = new ArrayList<>(eq);
            en.sort((x, y) -> {
                int r = Long.compare(x.getValue().n, y.getValue().n);
                return r != 0 ? r : UTF8.compare(x.getKey(), y.getKey());
            });
            compare(cn.useIndex("bynamen", Item.class).eq(nm).kvs(), en, what + " bynamen eq");
            long from = rnd.nextInt(1000) - 500;
            List<Map.Entry<String, Item>> enf = new ArrayList<>();
            for (Map.Entry<String, Item> e : en) if (e.getValue().n >= from) enf.add(e);
            compare(cn.useIndex("bynamen", Item.class).eq(nm).from(from, true).kvs(), enf, what + " bynamen from " + from);
        }
        List<Map.Entry<String, Item>> all2 = new ArrayList<>(exp.entrySet());
        all2.sort((x, y) -> {
            int r = UTF8.compare(x.getValue().name, y.getValue().name);
            if (r != 0) return r;
            r = Long.compare(x.getValue().n, y.getValue().n);
            return r != 0 ? r : UTF8.compare(x.getKey(), y.getKey());
        });
        compare(cn.useIndex("bynamen", Item.class).kvs(), all2, what + " bynamen");
    }

    static void compare(Iterable<Kv<Item>> it, List<Map.Entry<String, Item>> exp, String what) {
        int i = 0;
        for (Kv<Item> kv : it) {
            if (i >= exp.size()) throw new Common.Fail(what + ": extra entry " + kv.key() + " " + kv.value() + " at " + i);
            Map.Entry<String, Item> e = exp.get(i);
            if (!kv.key().equals(e.getKey()) || !kv.value().equals(e.getValue()))
                throw new Common.Fail(what + ": index " + i + " got " + kv.key() + " " + kv.value() + ", expected " + e.getKey()
                        + " " + e.getValue());
            i++;
        }
        if (i != exp.size()) throw new Common.Fail(what + ": " + i + " entries, expected " + exp.size() + "; missing "
                + exp.get(i).getKey() + " " + exp.get(i).getValue());
        checks++;
    }
}
