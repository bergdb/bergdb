import bergdb.pub.*;
import bergdb.pub.util.LookupTimeNotAvailableException;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;

/** Functional history/reclaim/scan checks. Usage: D2ScanHistory DIR SEED [rounds]. */
public final class D2ScanHistory {
    static final Comparator<String> ORDER = (a, b) -> Arrays.compareUnsigned(
            a.getBytes(StandardCharsets.UTF_8), b.getBytes(StandardCharsets.UTF_8));
    static final String[] DIRS = {"/events/", "/events/sub/", "/v1.2/", "/"};
    static final String[] ODD = {"a", "aa", "\u0000", "\u0001", "å", "中", "\ue000", "😀", "𐀀", "z"};
    final Map<String, NavigableMap<Long, String>> history = new HashMap<>();
    final Map<Long, Map<String, String>> transactions = new HashMap<>();
    final List<Long> times = new ArrayList<>();
    final Random random;
    long checks, cuts, lastFirst;
    D2ScanHistory(long seed) { random = new Random(seed); }
    static void check(boolean ok, String m) { if (!ok) throw new IllegalStateException(m); }
    String at(String k, long time) {
        var h = history.get(k); var v = h == null ? null : h.floorEntry(time);
        return v == null ? null : v.getValue();
    }
    NavigableMap<String, String> state(long t, String dir) {
        NavigableMap<String, String> out = new TreeMap<>(ORDER);
        for (String k : history.keySet())
            if (k.substring(0, k.lastIndexOf('/') + 1).equals(dir)) {
                String v = at(k, t); if (v != null) out.put(k, v);
            }
        return out;
    }
    void apply(Map<String, String> ops, long t) {
        Map<String, String> stored = new HashMap<>();
        for (var e : ops.entrySet()) {
            if (e.getValue() != null || at(e.getKey(), t - 1) != null) stored.put(e.getKey(), e.getValue());
            history.computeIfAbsent(e.getKey(), k -> new TreeMap<>()).put(t, e.getValue());
        }
        transactions.put(t, stored); times.add(t);
    }
    static String key(int id) { return DIRS[id % DIRS.length] + ODD[id % ODD.length] + String.format(Locale.ROOT, "%04d", id) + ".txt"; }
    List<String> expected(long t, String dir, String start, boolean incl, boolean backward) {
        List<String> out = new ArrayList<>();
        for (var e : state(t, dir).entrySet()) {
            String name = e.getKey().substring(dir.length()); int cmp = start == null ? 0 : ORDER.compare(name, start);
            if (start == null || (backward ? cmp < 0 : cmp > 0) || incl && cmp == 0)
                out.add(e.getKey() + "=" + e.getValue());
        }
        if (backward) Collections.reverse(out); return out;
    }
    void scan(Connection c, long t, String dir, String start, boolean inclusive, boolean backward) {
        UsePrimaryBuilder<String> b = c.usePrimary(String.class).dir(dir);
        if (start != null) b.startAt(start);
        b.inclusive(inclusive); if (backward) b.backward();
        List<String> want = expected(t, dir, start, inclusive, backward);
        Iterable<Kv<String>> iterable = b.kvs();
        for (int repeat = 0; repeat < 2; repeat++) {
            List<String> got = new ArrayList<>(); Iterator<Kv<String>> it = iterable.iterator();
            while (it.hasNext()) {
                check(it.hasNext(), "hasNext not idempotent"); Kv<String> e = it.next();
                got.add(e.key() + "=" + e.value());
            }
            check(!it.hasNext(), "exhausted iterator changed");
            try { it.next(); throw new IllegalStateException("next succeeded after exhaustion"); }
            catch (NoSuchElementException good) { }
            check(got.equals(want), "scan mismatch t=" + t + " dir=" + dir + " start=" + start
                    + " back=" + backward + " expected=" + want.size() + " got=" + got.size()); checks++;
        }
        List<String> values = new ArrayList<>(); for (String v : b.objects()) values.add(v);
        check(values.equals(want.stream().map(e -> e.substring(e.indexOf('=') + 1)).toList()), "objects differs from kvs");
    }
    void verify(Database db, long t) {
        Connection c = db.newConnection(); c.setLookupTime(Time.units(t));
        for (int n = 0; n < 20; n++) {
            String k = key(random.nextInt(260)); String want = at(k, t), got = c.get(k, String.class);
            check(Objects.equals(want, got), "get mismatch at " + t + " " + k);
            check(c.exists(k) == (want != null), "exists mismatch");
            if (want != null) {
                byte[] raw = c.get(k, byte[].class);
                check(Arrays.equals(want.getBytes(StandardCharsets.UTF_8), raw), "bytes differ");
                check(want.equals(c.get(k, Object.class)), "suffix did not select String");
                long written = history.get(k).floorKey(t);
                if (written >= db.getFirstAvailableLookupTime().units()) {
                    TransactionInfo info = c.transactionInfo(); check(info.time().units() == written, "original transaction time lost");
                    Map<String, String> entries = new HashMap<>();
                    for (Kv<byte[]> e : info.kvs()) entries.put(e.key(), e.value() == null ? null : new String(e.value(), StandardCharsets.UTF_8));
                    check(entries.equals(transactions.get(written)), "transaction KVs mismatch at " + written);
                }
            }
        }
        for (String dir : DIRS) {
            scan(c, t, dir, null, true, false); scan(c, t, dir, null, true, true);
            String start = ODD[random.nextInt(ODD.length)] + "0100.txt";
            scan(c, t, dir, start, random.nextBoolean(), random.nextBoolean());
        }
        checks++;
    }
    void boundaries(Database db) {
        long first = db.getFirstAvailableLookupTime().units();
        check(first >= lastFirst, "first available time moved backward within run");
        if (first > lastFirst) cuts++;
        lastFirst = first;
        verify(db, first); verify(db, db.currentTime().units());
        if (first > 0) {
            Connection c = db.newConnection(); c.setLookupTime(Time.units(first - 1));
            try { c.get(key(1), String.class); throw new IllegalStateException("get accepted expired time"); }
            catch (LookupTimeNotAvailableException good) { }
            try { c.usePrimary(String.class).dir("/events/").kvs().iterator().hasNext();
                throw new IllegalStateException("scan accepted expired time"); }
            catch (LookupTimeNotAvailableException good) { }
        }
        if (!times.isEmpty()) {
            long t = times.get(random.nextInt(times.size()));
            if (t >= first) { verify(db, t); if (t > first) verify(db, t - 1); }
        }
    }
    public static void main(String[] args) throws Exception {
        String path = args[0]; long seed = Long.parseLong(args[1]); int rounds = args.length > 2 ? Integer.parseInt(args[2]) : 2200;
        check(!Files.exists(Path.of(path)), "use a fresh directory");
        System.out.println("Kind: functional; D2ScanHistory seed=" + seed + " rounds=" + rounds);
        D2ScanHistory app = new D2ScanHistory(seed); TestClock clock = new TestClock(); clock.setTime(Time.utc("2020-01-01"));
        for (int phase = 0; phase < 3; phase++) {
            try (Database db = (phase == 0 ? Factory.database().create(path) : Factory.database().open(path)).clock(clock).cacheSizeInMb(32).start()) {
                if (phase == 0) { db.setStartupDistanceInMb(5); db.setRetainDuration(Duration.seconds(3)); }
                else {
                    check(db.getFirstAvailableLookupTime().units() == app.lastFirst, "close/open changed first lookup time");
                    check(db.getStartupDistanceInMb() == 5 && db.getRetainDuration().equals(Duration.seconds(3)), "settings not persisted");
                    app.boundaries(db);
                }
                Connection c = db.connection(); c.setEnableKeyReplace(true);
                int end = (phase + 1) * rounds / 3;
                for (int round = phase * rounds / 3; round < end; round++) {
                    clock.setTime(Time.units(clock.getTime() + 1000000L));
                    c.setLookupTime(Time.MAX);
                    UsePrimaryBuilder<String> pinned = null; List<String> pinnedWant = null;
                    if (round % 17 == 0) {
                        c.freezeLookupTime(); pinned = c.usePrimary(String.class).dir("/events/");
                        pinnedWant = app.expected(c.getLookupTime().units(), "/events/", null, true, false);
                    }
                    Map<String, String> ops = new LinkedHashMap<>(); WBuilder w = c.w();
                    for (int j = 0; j < 13; j++) {
                        String key = key(app.random.nextInt(260));
                        if (app.random.nextInt(4) == 0) { w.delete(key); ops.put(key, null); }
                        else {
                            String v = round + ":" + j + ":" + "x".repeat(1600 + app.random.nextInt(1200));
                            w.put(key, "temporary"); w.delete(key); w.put(key, v); ops.put(key, v);
                        }
                    }
                    boolean replaced = round % 31 == 0;
                    if (replaced) w.put("/events/${transactionTime}.txt", "replace:" + round);
                    long t = w.execute().getTime().units();
                    if (replaced) ops.put("/events/" + String.format(Locale.ROOT, "%018d", t) + ".txt", "replace:" + round);
                    app.apply(ops, t);
                    if (pinned != null) {
                        List<String> got = new ArrayList<>(); for (Kv<String> e : pinned.kvs()) got.add(e.key() + "=" + e.value());
                        check(got.equals(pinnedWant), "scan builder changed lookup time after write"); app.checks++;
                    }
                    if (round % 80 == 0) { db.sync(); app.boundaries(db); }
                }
                for (int n = 0; n < 5; n++) {
                    clock.setTime(Time.units(clock.getTime() + 40000000L));
                    db.maintain(100000);
                    db.sync(); app.boundaries(db);
                }
                app.lastFirst = db.getFirstAvailableLookupTime().units();
                System.out.println("phase=" + phase + " cuts=" + app.cuts + " checks=" + app.checks + " first=" + app.lastFirst);
            }
        }
        System.out.println("OK D2ScanHistory transactions=" + rounds + " cuts=" + app.cuts + " checks=" + app.checks + " restarts=2");
    }
}
