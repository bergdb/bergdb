import bergdb.pub.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;

/** Functional object and secondary-index checks. Usage: D3ObjectIndex DIR SEED [updates] [retain]. */
public final class D3ObjectIndex {
    public static class Detail {
        public long weight; public String memo;
        public Detail() { }
        Detail(long w, String m) { weight = w; memo = m; }
    }
    public static class Item {
        public long id, score; public String name; public byte[] tag; public double ratio;
        public Detail detail; public int[] numbers; public char[] characters; public String[] aliases;
        public byte[] payload;
        public Item() { }
    }
    record Value(Item item, String text) { }
    enum Field { NAME, SCORE, TAG, RATIO, WEIGHT }
    record Snapshot(long time, Map<String, Value> values, Map<String, List<Field>> indexes) { }
    record Query(List<Object> eq, Object from, boolean fi, Object to, boolean ti, Object prefix, boolean back) { }
    static final Comparator<String> TEXT = (a, b) -> Arrays.compareUnsigned(a.getBytes(StandardCharsets.UTF_8), b.getBytes(StandardCharsets.UTF_8));
    static final String[] NAMES = {"", "A", "Aa", "A\u0000", "A\u0001", "Å", "中", "\ue000", "𐀀", "😀"};
    static final byte[][] TAGS = {{}, {0}, {1}, {0, 1}, {1, 0}, {2}, {(byte) 0x80}, {(byte) 0xff}, {2, 0, 1}};
    static final long[] SCORES = {Long.MIN_VALUE, -100, -1, 0, 1, 100, Long.MAX_VALUE};
    static final double[] RATIOS = {Double.NEGATIVE_INFINITY, -Double.MAX_VALUE, -1, -Double.MIN_VALUE,
            -0.0, 0.0, Double.MIN_VALUE, 0.1f, 1, Double.MAX_VALUE, Double.POSITIVE_INFINITY, Double.NaN};
    final Map<String, Value> oracle = new HashMap<>();
    final Map<String, List<Field>> indexes = new LinkedHashMap<>();
    final List<Snapshot> snapshots = new ArrayList<>();
    final Random random; final boolean retain; long scans, gets, expired, cuts, lastFirst;
    D3ObjectIndex(long seed, boolean retain) { random = new Random(seed); this.retain = retain; }
    static void check(boolean ok, String m) { if (!ok) throw new IllegalStateException(m); }
    static String key(int n) { return "/catalog/" + NAMES[n % NAMES.length] + String.format(Locale.ROOT, "%04d", n); }
    Item item(int id) {
        Item i = new Item(); i.id = id; i.score = SCORES[random.nextInt(SCORES.length)];
        i.name = random.nextInt(9) == 0 ? null : NAMES[random.nextInt(NAMES.length)];
        i.tag = random.nextInt(9) == 0 ? null : TAGS[random.nextInt(TAGS.length)].clone();
        i.ratio = RATIOS[random.nextInt(RATIOS.length)];
        i.detail = random.nextInt(9) == 0 ? null : new Detail(SCORES[random.nextInt(SCORES.length)], "nested:" + id);
        i.numbers = new int[]{Integer.MIN_VALUE, id, Integer.MAX_VALUE};
        i.characters = new char[]{0, 'A', '\ud800', '\udfff'}; i.aliases = new String[]{"", "alias:" + id, "😀"};
        i.payload = new byte[retain ? 12000 + random.nextInt(8001) : 0]; random.nextBytes(i.payload);
        return i;
    }
    static Item copy(Item i) {
        Item c = new Item(); c.id = i.id; c.score = i.score; c.name = i.name; c.tag = i.tag == null ? null : i.tag.clone(); c.ratio = i.ratio;
        c.detail = i.detail == null ? null : new Detail(i.detail.weight, i.detail.memo);
        c.numbers = i.numbers.clone(); c.characters = i.characters.clone(); c.aliases = i.aliases.clone();
        c.payload = i.payload.clone(); return c;
    }
    static void same(Item a, Item b, String where) {
        check(b != null && a.id == b.id && a.score == b.score && Objects.equals(a.name, b.name)
                && Arrays.equals(a.tag, b.tag) && Double.doubleToLongBits(a.ratio) == Double.doubleToLongBits(b.ratio)
                && Arrays.equals(a.numbers, b.numbers) && Arrays.equals(a.characters, b.characters) && Arrays.equals(a.aliases, b.aliases)
                && Arrays.equals(a.payload, b.payload)
                && (a.detail == null ? b.detail == null : b.detail != null && a.detail.weight == b.detail.weight && Objects.equals(a.detail.memo, b.detail.memo)),
                "object mismatch " + where);
    }
    static Object field(Item i, Field f) {
        return switch (f) { case NAME -> i.name; case SCORE -> i.score; case TAG -> i.tag;
            case RATIO -> Double.isNaN(i.ratio) ? null : i.ratio == 0 ? 0.0 : i.ratio;
            case WEIGHT -> i.detail == null ? null : i.detail.weight; };
    }
    static int cmp(Object a, Object b) {
        if (a instanceof String s) return TEXT.compare(s, (String) b);
        if (a instanceof byte[] bytes) return Arrays.compareUnsigned(bytes, (byte[]) b);
        if (a instanceof Long l) return Long.compare(l, (Long) b);
        double x = (Double) a, y = (Double) b;
        return Double.compare(x == 0 ? 0 : x, y == 0 ? 0 : y);
    }
    static int encoded(Object o) {
        if (o instanceof Long || o instanceof Double) return 8;
        byte[] b = o instanceof String s ? s.getBytes(StandardCharsets.UTF_8) : (byte[]) o;
        int size = 1 + b.length; for (byte v : b) if (v == 0 || v == 1) size++; return size;
    }
    static List<Object> levels(Item item, List<Field> fields) {
        List<Object> list = new ArrayList<>(); int bytes = 0;
        for (Field f : fields) { Object o = field(item, f); if (o == null) return null; bytes += encoded(o); list.add(o); }
        return bytes <= 111 ? list : null;
    }
    void create(Database db, String name, List<Field> fields) {
        IndexBuilder b = db.indexBuilder(name).dir("/catalog/");
        for (Field f : fields) switch (f) {
            case NAME -> b.type("string").field("name"); case SCORE -> b.type("long").field("score");
            case TAG -> b.type("bytes").field("tag"); case RATIO -> b.type("double").field("ratio");
            case WEIGHT -> b.type("long").nestedField(new String[]{"detail", "weight"});
        }
        b.start().join(); indexes.put(name, List.copyOf(fields)); save(db);
    }
    Snapshot save(Database db) {
        Snapshot s = new Snapshot(db.currentTime().units(), Map.copyOf(oracle), Map.copyOf(indexes)); snapshots.add(s); return s;
    }
    static boolean starts(Object value, Object prefix) {
        if (value instanceof String s) return s.startsWith((String) prefix);
        byte[] b = (byte[]) value, p = (byte[]) prefix;
        return b.length >= p.length && Arrays.equals(b, 0, p.length, p, 0, p.length);
    }
    List<String> expected(Snapshot s, List<Field> fields, Query q) {
        List<String> keys = new ArrayList<>();
        for (var e : s.values.entrySet()) {
            Item i = e.getValue().item; List<Object> lev = i == null ? null : levels(i, fields); if (lev == null) continue;
            boolean take = true;
            for (int n = 0; n < q.eq.size(); n++) if (cmp(lev.get(n), q.eq.get(n)) != 0) take = false;
            if (q.eq.size() < lev.size()) {
                Object v = lev.get(q.eq.size());
                if (q.from != null) { int c = cmp(v, q.from); if (c < 0 || c == 0 && !q.fi) take = false; }
                if (q.to != null) { int c = cmp(v, q.to); if (c > 0 || c == 0 && !q.ti) take = false; }
                if (q.prefix != null && !starts(v, q.prefix)) take = false;
            }
            if (take) keys.add(e.getKey());
        }
        keys.sort((a, b) -> {
            List<Object> x = levels(s.values.get(a).item, fields), y = levels(s.values.get(b).item, fields);
            for (int n = 0; n < fields.size(); n++) { int c = cmp(x.get(n), y.get(n)); if (c != 0) return c; }
            return TEXT.compare(a, b);
        });
        if (q.back) Collections.reverse(keys); return keys;
    }
    static void eq(UseIndexBuilder<Item> b, Object o) {
        if (o instanceof String s) b.eq(s); else if (o instanceof byte[] v) b.eq(v); else if (o instanceof Long l) b.eq(l); else b.eq((Double) o);
    }
    static void bound(UseIndexBuilder<Item> b, Object o, boolean inclusive, boolean lower) {
        if (o instanceof String s) { if (lower) b.from(s, inclusive); else b.to(s, inclusive); }
        else if (o instanceof byte[] v) { if (lower) b.from(v, inclusive); else b.to(v, inclusive); }
        else if (o instanceof Long l) { if (lower) b.from(l, inclusive); else b.to(l, inclusive); }
        else { if (lower) b.from((Double) o, inclusive); else b.to((Double) o, inclusive); }
    }
    void query(Connection c, Snapshot s, String index, List<Field> fields, Query q) {
        UseIndexBuilder<Item> b = c.useIndex(index, Item.class);
        if (q.back) b.backward(); for (Object o : q.eq) eq(b, o);
        if (q.from != null) bound(b, q.from, q.fi, true); if (q.to != null) bound(b, q.to, q.ti, false);
        if (q.prefix instanceof String p) b.prefix(p); else if (q.prefix != null) b.prefix((byte[]) q.prefix);
        List<String> want = expected(s, fields, q);
        for (int repeat = 0; repeat < 2; repeat++) {
            List<String> got = new ArrayList<>(); Iterator<Kv<Item>> it = b.kvs().iterator();
            while (it.hasNext()) {
                check(it.hasNext(), "unstable hasNext"); Kv<Item> e = it.next(); got.add(e.key());
                same(s.values.get(e.key()).item, e.value(), "index value " + index + " " + e.key());
            }
            check(got.equals(want), "index mismatch " + index + " at=" + s.time + " query=" + q
                    + " expected=" + want + " got=" + got); scans++;
        }
        List<Long> gotIds = new ArrayList<>(); for (Item i : b.objects()) gotIds.add(i.id);
        check(gotIds.equals(want.stream().map(k -> s.values.get(k).item.id).toList()), "objects not same as kvs");
    }
    void verify(Database db, Snapshot s) {
        Connection c = db.newConnection(); c.setLookupTime(Time.units(s.time));
        long first = db.getFirstAvailableLookupTime().units();
        check(first >= lastFirst, "first available time moved backwards");
        if (first > lastFirst) cuts++;
        lastFirst = first;
        if (s.time < first) {
            boolean refused = false;
            try { c.get(key(0), Item.class); }
            catch (bergdb.pub.util.LookupTimeNotAvailableException good) { refused = true; }
            check(refused, "expired object history accepted"); expired++; return;
        }
        List<String> primary = new ArrayList<>();
        for (Kv<Item> e : c.usePrimary(Item.class).dir("/catalog/").kvs()) {
            check(s.values.containsKey(e.key()) && s.values.get(e.key()).item != null, "extra primary object");
            same(s.values.get(e.key()).item, e.value(), "primary " + e.key()); primary.add(e.key());
        }
        List<String> wanted = s.values.entrySet().stream().filter(e -> e.getValue().item != null).map(Map.Entry::getKey).sorted(TEXT).toList();
        check(primary.equals(wanted), "primary object membership/order mismatch");
        List<String> text = new ArrayList<>(); for (Kv<String> e : c.usePrimary(String.class).dir("/catalog/").kvs()) {
            check(s.values.containsKey(e.key()) && Objects.equals(s.values.get(e.key()).text, e.value()), "primary text mismatch"); text.add(e.key());
        }
        check(text.equals(s.values.entrySet().stream().filter(e -> e.getValue().item == null).map(Map.Entry::getKey).sorted(TEXT).toList()), "text membership/order mismatch");
        for (int n = 0; n < 20; n++) {
            String k = key(random.nextInt(180)); Value v = s.values.get(k);
            check(c.exists(k) == (v != null), "exists mismatch");
            if (v == null) check(c.get(k, Item.class) == null, "absent object not null");
            else if (v.item != null) {
                same(v.item, c.get(k, Item.class), "get " + k);
                DbObject raw = c.get(k, DbObject.class); check(raw.getLong("score") == v.item.score && raw.getLong("id") == v.item.id, "stored fields differ");
                check(c.get(k, Object.class) instanceof DbObject, "object guessed incorrectly");
            } else check(v.text.equals(c.get(k, String.class)), "text get mismatch"); gets++;
        }
        for (var definition : s.indexes.entrySet()) {
            String name = definition.getKey(); List<Field> fields = definition.getValue();
            query(c, s, name, fields, new Query(List.of(), null, true, null, true, null, false));
            query(c, s, name, fields, new Query(List.of(), null, true, null, true, null, true));
            List<List<Object>> choices = new ArrayList<>();
            for (Value v : s.values.values()) if (v.item != null) { List<Object> l = levels(v.item, fields); if (l != null) choices.add(l); }
            if (choices.isEmpty()) continue;
            for (int n = 0; n < 6; n++) {
                List<Object> lev = choices.get(random.nextInt(choices.size())); int eqs = random.nextInt(fields.size() + 1);
                List<Object> eq = lev.subList(0, eqs); Object from = null, to = null, prefix = null;
                if (eqs < fields.size()) {
                    Object a = lev.get(eqs), b = choices.get(random.nextInt(choices.size())).get(eqs);
                    if (n % 3 == 0 && (a instanceof String || a instanceof byte[]))
                        prefix = n % 2 == 0 ? a instanceof String ? "" : new byte[0] : a;
                    else { from = a; to = b; }
                }
                query(c, s, name, fields, new Query(eq, from, random.nextBoolean(), to, random.nextBoolean(), prefix, random.nextBoolean()));
            }
        }
    }
    public static void main(String[] args) throws Exception {
        String path = args[0]; long seed = Long.parseLong(args[1]); int count = args.length > 2 ? Integer.parseInt(args[2]) : 1200;
        boolean retain = args.length > 3 && args[3].equals("retain");
        check(!Files.exists(Path.of(path)), "use a fresh directory");
        System.out.println("Kind: functional; D3ObjectIndex seed=" + seed + " updates=" + count + " retain=" + retain);
        D3ObjectIndex app = new D3ObjectIndex(seed, retain);
        TestClock clock = new TestClock(); clock.setTime(Time.utc("2020-01-01"));
        for (int phase = 0; phase < 3; phase++) {
            DatabaseBuilder builder = phase == 0 ? Factory.database().create(path) : Factory.database().open(path);
            if (retain) builder.clock(clock);
            try (Database db = builder.cacheSizeInMb(64).start()) {
                Connection c = db.connection();
                if (phase == 0) {
                    if (retain) { db.setStartupDistanceInMb(5); db.setRetainDuration(Duration.seconds(3)); }
                    for (int n = 0; n < 180; n++) { Item item = app.item(n); c.put(key(n), item); app.oracle.put(key(n), new Value(copy(item), null)); }
                    Item oversized = app.item(10000); oversized.name = "x".repeat(150); c.put(key(181), oversized); app.oracle.put(key(181), new Value(copy(oversized), null));
                    app.create(db, "group", List.of(Field.NAME, Field.SCORE));
                    app.create(db, "blob", List.of(Field.TAG, Field.RATIO, Field.SCORE));
                    app.create(db, "metric", List.of(Field.WEIGHT));
                    app.create(db, "score", List.of(Field.SCORE, Field.NAME, Field.RATIO));
                    app.create(db, "eight", List.of(Field.SCORE, Field.RATIO, Field.NAME, Field.TAG,
                            Field.WEIGHT, Field.SCORE, Field.NAME, Field.RATIO));
                } else {
                    for (String name : app.indexes.keySet()) db.indexJob(name).join();
                    app.verify(db, app.snapshots.get(app.snapshots.size() - 1));
                }
                int end = (phase + 1) * count / 3;
                for (int n = phase * count / 3; n < end; n++) {
                    if (retain) clock.setTime(Time.units(clock.getTime() + 2000000L));
                    String k = key(app.random.nextInt(180));
                    if (n % 7 == 0) { c.delete(k); app.oracle.remove(k); }
                    else if (n % 11 == 0) { String t = "plain:" + n; c.put(k, t); app.oracle.put(k, new Value(null, t)); }
                    else {
                        Item i = app.item(n + 200); Item saved = copy(i);
                        if (n % 5 == 0) c.put(k, DbObject.toDbObject(i).getBytes());
                        else if (n % 3 == 0) c.rw(env -> { env.delete(k); env.put(k, i); });
                        else c.w().put(k, "temporary").put(k, i).execute();
                        app.oracle.put(k, new Value(saved, null));
                        i.score = 424242; i.name = "changed after put"; if (i.tag != null) Arrays.fill(i.tag, (byte) 42);
                        i.numbers[1] = -1; i.aliases[0] = "changed";
                    }
                    if (n % 80 == 0) {
                        Snapshot now = app.save(db); app.verify(db, now);
                        app.verify(db, app.snapshots.get(app.random.nextInt(app.snapshots.size())));
                    }
                }
                Snapshot before = app.save(db); app.verify(db, before);
                Connection old = db.newConnection(); old.setLookupTime(Time.units(before.time));
                UseIndexBuilder<Item> pinned = old.useIndex("metric", Item.class);
                List<String> wantPinned = app.expected(before, before.indexes.get("metric"), new Query(List.of(), null, true, null, true, null, false));
                db.deleteIndex("metric"); app.indexes.remove("metric"); Snapshot deleted = app.save(db);
                try { c.setLookupTime(Time.MAX); c.useIndex("metric", Item.class); throw new IllegalStateException("deleted index still usable"); }
                catch (NoSuchIndexException good) { }
                app.create(db, "metric", List.of(phase % 2 == 0 ? Field.RATIO : Field.WEIGHT));
                List<String> gotPinned = new ArrayList<>(); for (Kv<Item> e : pinned.kvs()) gotPinned.add(e.key());
                check(gotPinned.equals(wantPinned), "old builder changed index incarnation");
                app.verify(db, before); app.verify(db, deleted); app.verify(db, app.save(db)); db.sync();
                if (retain) for (int n = 0; n < 6; n++) {
                    clock.setTime(Time.units(clock.getTime() + 40000000L));
                    int steps = 0; while (db.maintain()) check(++steps < 10000, "maintenance did not quiesce");
                    db.sync(); app.verify(db, app.save(db));
                    app.verify(db, app.snapshots.get(app.random.nextInt(app.snapshots.size())));
                }
                System.out.println("phase=" + phase + " scans=" + app.scans + " gets=" + app.gets + " snapshots=" + app.snapshots.size()
                        + " cuts=" + app.cuts + " expired=" + app.expired);
            }
        }
        try (Database db = Factory.database().open(path).cacheSizeInMb(64).start()) {
            for (Snapshot s : app.snapshots) app.verify(db, s);
        }
        System.out.println("OK D3ObjectIndex scans=" + app.scans + " gets=" + app.gets + " cuts=" + app.cuts + " expired=" + app.expired + " restarts=3");
    }
}
