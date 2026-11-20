import bergdb.pub.*;
import bergdb.pub.util.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;
import java.util.concurrent.*;

/** Functional online index-build checks. Usage: D8OnlineIndex DIR SEED [rounds] [rows]. */
public final class D8OnlineIndex {
    public static class Row {
        public long id, revision, value; public String group; public byte[] payload;
        public Row() { }
    }
    record Snapshot(long time, Map<String, Row> values, boolean text) { }
    static final String[] GROUPS = {"", "A", "A\u0000", "A\u0001", "Å", "中", "\ue000", "𐀀", "😀"};
    static final Comparator<String> ORDER = (a, b) -> Arrays.compareUnsigned(a.getBytes(StandardCharsets.UTF_8), b.getBytes(StandardCharsets.UTF_8));
    final Map<String, Row> oracle = new HashMap<>();
    final List<Snapshot> snapshots = new ArrayList<>();
    final Random random; long scans, rowsChecked, canceled, resumed;
    D8OnlineIndex(long seed) { random = new Random(seed); }
    static void check(boolean ok, String m) { if (!ok) throw new IllegalStateException(m); }
    static String key(int id) { return "/rows/" + GROUPS[id % GROUPS.length] + String.format(Locale.ROOT, "%06d", id); }
    Row row(int id, long revision) {
        Row r = new Row(); r.id = id; r.revision = revision; r.value = random.nextInt(31) - 15;
        r.group = random.nextInt(8) == 0 ? null : GROUPS[random.nextInt(GROUPS.length)];
        r.payload = new byte[256 + random.nextInt(1025)]; random.nextBytes(r.payload); return r;
    }
    static void same(Row want, Row got, String where) {
        check(want != null && got != null && want.id == got.id && want.revision == got.revision && want.value == got.value
                && Objects.equals(want.group, got.group) && Arrays.equals(want.payload, got.payload), "row differs " + where);
    }
    static Object level(Row r, boolean text) { return text ? r.group : r.value; }
    static int cmp(Object a, Object b) { return a instanceof String s ? ORDER.compare(s, (String) b) : Long.compare((Long) a, (Long) b); }
    static Job start(Database db, String name, boolean text) {
        return db.indexBuilder(name).dir("/rows/").type(text ? "string" : "long").field(text ? "group" : "value").start();
    }
    Snapshot snapshot(Database db, boolean text) {
        Snapshot s = new Snapshot(db.currentTime().units(), Map.copyOf(oracle), text); snapshots.add(s); return s;
    }
    List<String> expected(Snapshot s, Object eq, Object from, boolean fi, Object to, boolean ti, String prefix, boolean back) {
        List<String> keys = new ArrayList<>();
        for (var e : s.values.entrySet()) {
            Object v = level(e.getValue(), s.text); if (v == null) continue;
            if (eq != null && cmp(v, eq) != 0) continue;
            if (from != null && (cmp(v, from) < 0 || cmp(v, from) == 0 && !fi)) continue;
            if (to != null && (cmp(v, to) > 0 || cmp(v, to) == 0 && !ti)) continue;
            if (prefix != null && !((String) v).startsWith(prefix)) continue;
            keys.add(e.getKey());
        }
        keys.sort((a, b) -> { int c = cmp(level(s.values.get(a), s.text), level(s.values.get(b), s.text)); return c == 0 ? ORDER.compare(a, b) : c; });
        if (back) Collections.reverse(keys); return keys;
    }
    void query(Connection c, String name, Snapshot s, Object eq, Object from, boolean fi, Object to, boolean ti, String prefix, boolean back) {
        UseIndexBuilder<Row> b = c.useIndex(name, Row.class); if (back) b.backward();
        if (eq instanceof String v) b.eq(v); else if (eq != null) b.eq((Long) eq);
        if (from instanceof String v) b.from(v, fi); else if (from != null) b.from((Long) from, fi);
        if (to instanceof String v) b.to(v, ti); else if (to != null) b.to((Long) to, ti);
        if (prefix != null) b.prefix(prefix);
        List<String> want = expected(s, eq, from, fi, to, ti, prefix, back), got = new ArrayList<>();
        for (Kv<Row> e : b.kvs()) { same(s.values.get(e.key()), e.value(), name + " " + e.key()); got.add(e.key()); rowsChecked++; }
        check(want.equals(got), "online index membership/order differs " + name + " at=" + s.time); scans++;
    }
    void verify(Database db, String name, Snapshot s) {
        Connection c = db.newConnection(); c.setLookupTime(Time.units(s.time));
        List<String> primary = new ArrayList<>();
        for (Kv<Row> e : c.usePrimary(Row.class).dir("/rows/").kvs()) {
            same(s.values.get(e.key()), e.value(), "primary " + e.key()); primary.add(e.key()); rowsChecked++;
        }
        check(primary.equals(s.values.keySet().stream().sorted(ORDER).toList()), "primary differs from model");
        for (boolean back : new boolean[]{false, true}) {
            query(c, name, s, null, null, true, null, true, null, back);
            if (s.text) {
                query(c, name, s, "A", null, true, null, true, null, back);
                query(c, name, s, null, "A", false, "😀", true, null, back);
                query(c, name, s, null, null, true, null, true, "A", back);
                query(c, name, s, null, "😀", true, "", true, null, back);
            } else {
                query(c, name, s, 0L, null, true, null, true, null, back);
                query(c, name, s, null, -7L, false, 8L, true, null, back);
                query(c, name, s, null, 12L, true, -12L, true, null, back);
            }
        }
    }
    void writes(Database db, int round, int count, int cardinality) {
        Connection c = db.connection();
        for (int n = 0; n < count; n++) {
            int id = random.nextInt(cardinality + 100); String k = key(id);
            if (n % 7 == 0) { c.delete(k); oracle.remove(k); }
            else {
                Row r = row(id, 1L + round * count + n); Row previous = oracle.get(k);
                if (n % 3 == 0) c.rw(env -> {
                    Row actual = env.get(k, Row.class);
                    if (previous == null) check(actual == null, "RW expected absent row"); else same(previous, actual, "RW input");
                    env.delete(k); env.put(k, r);
                });
                else c.w().put(k, "temporary").put(k, r).execute();
                oracle.put(k, r);
            }
        }
    }
    void failedBuild(String path) {
        try (Database db = Factory.database().create(path).cacheSizeInMb(32).start()) {
            byte[] old = {'b', 'e', 'r', 'g', 'o', 1, 0, 0}; db.connection().put("/rows/old", old);
            Job failed = start(db, "format", false); boolean refused = false;
            for (int i = 0; i < 3; i++) {
                try { (i == 2 ? db.indexJob("format") : failed).join(); }
                catch (IndexBuildException e) {
                    check(e.getStatus().state() == JobStatus.State.FAILED && e.getCause() instanceof DataFormatException, "wrong failed-build cause");
                    refused = true;
                }
                check(refused, "format-1 build did not fail"); refused = false;
            }
            check(failed.getStatus().state() == JobStatus.State.FAILED, "status did not retain failure");
            Row replacement = row(100000, 1); db.connection().put("/rows/old", replacement);
            same(replacement, db.connection().get("/rows/old", Row.class), "replace after failed build"); db.sync();
        }
        try (Database db = Factory.database().open(path).cacheSizeInMb(32).start()) {
            db.indexJob("format").join(); int count = 0;
            for (Row row : db.connection().useIndex("format", Row.class).objects()) { check(row.id == 100000, "failed build did not resume correctly"); count++; }
            check(count == 1, "replaced row absent after resumed build");
        }
    }
    public static void main(String[] args) throws Exception {
        String path = args[0]; long seed = Long.parseLong(args[1]);
        int rounds = args.length > 2 ? Integer.parseInt(args[2]) : 6, cardinality = args.length > 3 ? Integer.parseInt(args[3]) : 2000;
        check(!Files.exists(Path.of(path)), "use a fresh directory");
        System.out.println("Kind: functional; D8OnlineIndex seed=" + seed + " rounds=" + rounds + " rows=" + cardinality);
        D8OnlineIndex app = new D8OnlineIndex(seed); ExecutorService writer = Executors.newSingleThreadExecutor();
        boolean text = false;
        try {
            for (int round = 0; round < rounds; round++) {
                DatabaseBuilder builder = round == 0 ? Factory.database().create(path) : Factory.database().open(path);
                try (Database db = builder.cacheSizeInMb(64).start()) {
                    if (round == 0) {
                        Connection c = db.connection();
                        for (int id = 0; id < cardinality; id++) { Row row = app.row(id, 0); c.put(key(id), row); app.oracle.put(key(id), row); }
                        start(db, "live", false).join();
                    } else { db.indexJob("live").join(); db.indexJob("resume" + (round - 1)).join(); app.resumed++; }
                    Snapshot before = app.snapshot(db, text); app.verify(db, "live", before);
                    Connection historic = db.newConnection(); historic.setLookupTime(Time.units(before.time));
                    UseIndexBuilder<Row> pinned = historic.useIndex("live", Row.class);
                    List<String> pinnedWant = app.expected(before, null, null, true, null, true, null, false);
                    db.deleteIndex("live"); text = !text; Job live = start(db, "live", text);
                    int stage = round;
                    Future<?> writes = writer.submit(() -> app.writes(db, stage, 1200, cardinality));
                    Job cancel = start(db, "canceled" + round, !text); db.deleteIndex("canceled" + round);
                    try { check(cancel.join().state() == JobStatus.State.ACTIVE, "deleted build neither failed nor completed"); }
                    catch (IndexBuildException e) {
                        check(e.getCause() == null && e.getStatus().reason().equals("deleted"), "wrong cancellation reason"); app.canceled++;
                    }
                    writes.get(5, TimeUnit.MINUTES); live.join();
                    Snapshot after = app.snapshot(db, text); app.verify(db, "live", after);
                    List<String> gotPinned = new ArrayList<>();
                    for (Kv<Row> e : pinned.kvs()) { same(before.values.get(e.key()), e.value(), "pinned old incarnation"); gotPinned.add(e.key()); }
                    check(gotPinned.equals(pinnedWant), "index deletion/recreation changed old iterator");
                    app.verify(db, "live", before);
                    start(db, "resume" + round, false); db.sync(); db.stop();
                    System.out.println("round=" + round + " scans=" + app.scans + " canceled=" + app.canceled + " resumed=" + app.resumed);
                }
            }
            try (Database db = Factory.database().open(path).cacheSizeInMb(64).start()) {
                db.indexJob("resume" + (rounds - 1)).join(); app.resumed++;
                app.verify(db, "live", app.snapshot(db, text));
                for (Snapshot s : app.snapshots) app.verify(db, "live", s);
            }
            app.failedBuild(path + "-format");
        } finally { writer.shutdownNow(); }
        System.out.println("OK D8OnlineIndex scans=" + app.scans + " rowsChecked=" + app.rowsChecked + " canceled=" + app.canceled + " resumed=" + app.resumed);
    }
}
