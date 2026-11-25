import bergdb.pub.*;
import bergdb.pub.util.*;
import java.nio.charset.StandardCharsets;
import java.util.*;
import java.util.concurrent.*;

/**
 * IndexQuery (031-02, e6). User indexes of the four level types, compound and nested, over
 * objects that two writer threads put, change, delete and replace by a String or bytes,
 * with absent fields, ties, -0.0, infinities, NaN, zero bytes and names outside the Basic
 * Multilingual Plane (code point order differs from Java's UTF-16 order there). Indexes are
 * created while the writers write, deleted and created again with another definition under
 * the same name. The oracle keeps every version of every key with its transaction's time
 * and the times when each index was surely active; after each phase it checks the listing
 * and, for each active index, full scans forward and backward, eq() on the first level with
 * a bound or a prefix on the next, ranges with each inclusive flag, prefixes of strings and
 * bytes, at the latest time and at older ones (an index is read at an older time with the
 * definition it had then), and across restarts with a cache budget of 4 MB.
 *
 * Usage: java IndexQuery DIR SEED PHASES
 */
public class IndexQuery {
    public static class Addr {
        public String city;
        public long zip;
        public Addr() {}
    }

    public static class Person {
        public String name;
        public Long age;
        public Double score;
        public byte[] tag;
        public Addr addr;
        public int[] arr;
        public Person() {}
    }

    static void fail(String m) {
        System.out.println("INDEXQUERY FAILED: " + m);
        System.out.flush();
        System.exit(1);
    }

    // A version: a Person, a String (non-object), or null (deleted).
    static final ConcurrentHashMap<String, TreeMap<Long, Object>> versions = new ConcurrentHashMap<>();

    static final class IndexDef {
        String name;
        String[] types;
        String[][] paths;
        long activeFrom;          // a time when it was surely active
        long activeTo = Long.MAX_VALUE;   // a time before which it was surely still active
        IndexDef(String name, String[] types, String[][] paths) { this.name = name; this.types = types; this.paths = paths; }
    }

    static final List<IndexDef> defs = new ArrayList<>();
    static Database db;
    static String dir;
    static Random r;
    static volatile boolean stop;
    static long nTx, nScans, nOld, nNoIndex;

    static final String[] NAMES = {"anna", "Anna", "anna-b", "bo", "åsa", "örjan", "～zed",
            "😀smile", "😀", "z", "", "a\u0000b", "\u0001x", "中文", "ann"};
    static final String[] CITIES = {"Lund", "Malmö", "Lund ", "Ystad", "🌍city", "lund"};

    static Person randomPerson(Random r) {
        Person p = new Person();
        if (r.nextInt(10) > 0) p.name = NAMES[r.nextInt(NAMES.length)] + (r.nextBoolean() ? "" : r.nextInt(5));
        if (r.nextInt(10) > 0) p.age = (long) (r.nextInt(30) - 5);
        int s = r.nextInt(12);
        if (s == 0) p.score = -0.0;
        else if (s == 1) p.score = 0.0;
        else if (s == 2) p.score = Double.POSITIVE_INFINITY;
        else if (s == 3) p.score = Double.NEGATIVE_INFINITY;
        else if (s == 4) p.score = Double.NaN;
        else if (s == 5) p.score = null;
        else p.score = (r.nextInt(200) - 100) / 8.0;
        if (r.nextInt(5) > 0) {
            p.tag = new byte[r.nextInt(5)];
            for (int i = 0; i < p.tag.length; i++) p.tag[i] = (byte) (r.nextInt(4) == 0 ? r.nextInt(3) : r.nextInt(256));
        }
        if (r.nextInt(4) > 0) {
            p.addr = new Addr();
            if (r.nextInt(6) > 0) p.addr.city = CITIES[r.nextInt(CITIES.length)];
            p.addr.zip = r.nextInt(10);
        }
        p.arr = new int[r.nextInt(3)];
        return p;
    }

    public static void main(String[] args) throws Exception {
        dir = args[0];
        long seed = Long.parseLong(args[1]);
        int phases = Integer.parseInt(args[2]);
        r = new Random(seed);
        System.out.println("IndexQuery seed " + seed + " phases " + phases);
        db = Factory.database().create(dir).start();
        createIndex(new IndexDef("by-age", new String[] {"long"}, new String[][] {{"age"}}));
        int defVariant = 0;
        for (int phase = 0; phase < phases; phase++) {
            stop = false;
            List<Thread> ws = new ArrayList<>();
            for (int w = 0; w < 2; w++) {
                final int wid = w;
                final long ws0 = seed * 100 + phase * 10 + w;
                Thread t = new Thread(() -> writer(wid, ws0));
                t.start();
                ws.add(t);
            }
            Thread.sleep(300 + r.nextInt(2000));
            // An index change while the writers write.
            int ev = r.nextInt(5);
            if (ev == 0 && !has("by-name-age")) createIndex(new IndexDef("by-name-age", new String[] {"string", "long"},
                    new String[][] {{"name"}, {"age"}}));
            else if (ev == 1 && !has("by-score")) createIndex(new IndexDef("by-score", new String[] {"double", "string"},
                    new String[][] {{"score"}, {"name"}}));
            else if (ev == 2 && !has("by-tag")) createIndex(new IndexDef("by-tag", new String[] {"bytes"},
                    new String[][] {{"tag"}}));
            else if (ev == 3 && !has("by-city")) createIndex(new IndexDef("by-city", new String[] {"string", "long"},
                    new String[][] {{"addr", "city"}, {"addr", "zip"}}));
            else if (ev == 4 && defs.size() > 1) {
                // Delete one, and create it again with another definition.
                IndexDef d = live().get(r.nextInt(live().size()));
                long before = db.connection().currentTime().units();
                db.deleteIndex(d.name);
                d.activeTo = before;
                defVariant++;
                IndexDef nd = defVariant % 2 == 0
                        ? new IndexDef(d.name, new String[] {"long", "bytes"}, new String[][] {{"age"}, {"tag"}})
                        : new IndexDef(d.name, new String[] {"string"}, new String[][] {{"addr", "city"}});
                createIndex(nd);
            }
            Thread.sleep(500 + r.nextInt(4000));
            stop = true;
            for (Thread t : ws) t.join();
            checkAll(Long.MAX_VALUE, "phase " + phase);
            for (int i = 0; i < 3; i++) checkOld("phase " + phase);
            if (phase % 4 == 3) {
                db.close();
                DatabaseBuilder b = Factory.database().open(dir);
                if (r.nextBoolean()) b.cacheSizeInMb(4);
                db = b.start();
                checkAll(Long.MAX_VALUE, "phase " + phase + " restarted");
                checkOld("phase " + phase + " restarted");
            }
            System.out.println("  phase " + phase + ": tx " + nTx + ", keys " + versions.size() + ", indexes " + live().size()
                    + ", scans " + nScans + " (older " + nOld + ", not active at the time " + nNoIndex + ")");
        }
        db.close();
        System.out.println("INDEXQUERY OK");
    }

    static boolean has(String name) {
        for (IndexDef d : defs) if (d.name.equals(name) && d.activeTo == Long.MAX_VALUE) return true;
        return false;
    }

    static List<IndexDef> live() {
        List<IndexDef> l = new ArrayList<>();
        for (IndexDef d : defs) if (d.activeTo == Long.MAX_VALUE) l.add(d);
        return l;
    }

    static void createIndex(IndexDef d) {
        IndexBuilder b = db.indexBuilder(d.name).dir("/p/");
        for (int i = 0; i < d.types.length; i++) {
            b.type(d.types[i]);
            if (d.paths[i].length == 1) b.field(d.paths[i][0]); else b.nestedField(d.paths[i]);
        }
        JobStatus st = b.start().join();
        if (st.state() != JobStatus.State.ACTIVE) fail("index " + d.name + " build ended " + st.state() + " " + st.reason());
        // A time after the build: at it and later the index is active.
        db.connection().put("/mark/m.txt", "x" + System.nanoTime());
        d.activeFrom = db.connection().currentTime().units();
        defs.add(d);
    }

    static void writer(int wid, long seed) {
        Random wr = new Random(seed);
        Connection c = db.connection();
        while (!stop) {
            int op = wr.nextInt(100);
            Map<String, Object> ops = new LinkedHashMap<>();
            if (op < 50) {
                ops.put(key(wid, wr), randomPerson(wr));
            } else if (op < 62) {
                ops.put(key(wid, wr), null);
            } else if (op < 67) {
                ops.put(key(wid, wr), "text" + wr.nextInt(10));
            } else {
                int n = 1 + wr.nextInt(40);
                for (int i = 0; i < n; i++) {
                    int k = wr.nextInt(10);
                    ops.put(key(wid, wr), k == 0 ? null : k == 1 ? "s" : randomPerson(wr));
                }
            }
            Transaction t;
            if (ops.size() == 1 && op < 67) {
                Map.Entry<String, Object> e = ops.entrySet().iterator().next();
                t = e.getValue() == null ? c.delete(e.getKey()) : c.put(e.getKey(), e.getValue());
            } else if (wr.nextBoolean()) {
                WBuilder w = c.w();
                for (Map.Entry<String, Object> e : ops.entrySet()) {
                    if (e.getValue() == null) w.delete(e.getKey()); else w.put(e.getKey(), e.getValue());
                }
                t = w.execute();
            } else {
                t = c.rw(env -> {
                    for (Map.Entry<String, Object> e : ops.entrySet()) {
                        env.get(e.getKey(), byte[].class);   // read before write
                        if (e.getValue() == null) env.delete(e.getKey()); else env.put(e.getKey(), e.getValue());
                    }
                });
            }
            long tt = t.getTime().units();
            for (Map.Entry<String, Object> e : ops.entrySet()) {
                TreeMap<Long, Object> v = versions.computeIfAbsent(e.getKey(), k -> new TreeMap<>());
                synchronized (v) { v.put(tt, e.getValue() == null ? DELETED : e.getValue()); }
            }
            synchronized (IndexQuery.class) { nTx++; }
            if (wr.nextInt(4) > 0) { try { Thread.sleep(1); } catch (InterruptedException ie) { return; } }
        }
    }

    static final Object DELETED = new Object();

    static String key(int wid, Random wr) {
        return "/p/w" + wid + "-" + NAMES[wr.nextInt(NAMES.length)].replace("\u0000", "0").replace("\u0001", "1") + wr.nextInt(150);
    }

    static Object at(String key, long t) {
        TreeMap<Long, Object> v = versions.get(key);
        if (v == null) return null;
        Map.Entry<Long, Object> e;
        synchronized (v) { e = v.floorEntry(t); }
        return e == null || e.getValue() == DELETED ? null : e.getValue();
    }

    static int cmpBytes(byte[] a, byte[] b) { return Arrays.compareUnsigned(a, b); }
    static byte[] utf8(String s) { return s.getBytes(StandardCharsets.UTF_8); }

    // A level's value of a person, or null for no entry.
    static Object level(Person p, String type, String[] path) {
        Object o = p;
        for (int i = 0; i < path.length; i++) {
            if (o == null) return null;
            if (o instanceof Person) {
                Person q = (Person) o;
                switch (path[i]) {
                case "name": o = q.name; break;
                case "age": o = q.age; break;
                case "score": o = q.score; break;
                case "tag": o = q.tag; break;
                case "addr": o = q.addr; break;
                default: return null;
                }
            } else if (o instanceof Addr) {
                Addr a = (Addr) o;
                o = path[i].equals("city") ? a.city : path[i].equals("zip") ? (Object) a.zip : null;
            } else return null;
        }
        if (o == null) return null;
        switch (type) {
        case "long": return o instanceof Long ? o : null;
        case "double": {
            if (!(o instanceof Double)) return null;
            double d = (Double) o;
            if (Double.isNaN(d)) return null;
            return d == 0.0 ? 0.0 : d;
        }
        case "string": return o instanceof String ? o : null;
        case "bytes": return o instanceof byte[] ? o : null;
        }
        return null;
    }

    static int cmpLevel(Object a, Object b) {
        if (a instanceof Long) return Long.compare((Long) a, (Long) b);
        if (a instanceof Double) return Double.compare((Double) a, (Double) b);
        if (a instanceof String) return cmpBytes(utf8((String) a), utf8((String) b));
        return cmpBytes((byte[]) a, (byte[]) b);
    }

    static final class Entry { String key; Object[] lv; Person p; }

    static List<Entry> entries(IndexDef d, long t) {
        List<Entry> l = new ArrayList<>();
        for (String k : versions.keySet()) {
            Object v = at(k, t);
            if (!(v instanceof Person)) continue;
            Person p = (Person) v;
            Object[] lv = new Object[d.types.length];
            boolean ok = true;
            for (int i = 0; i < lv.length; i++) {
                lv[i] = level(p, d.types[i], d.paths[i]);
                if (lv[i] == null) { ok = false; break; }
            }
            if (!ok) continue;
            Entry e = new Entry(); e.key = k; e.lv = lv; e.p = p;
            l.add(e);
        }
        l.sort((a, b) -> {
            for (int i = 0; i < a.lv.length; i++) {
                int x = cmpLevel(a.lv[i], b.lv[i]);
                if (x != 0) return x;
            }
            return cmpBytes(utf8(a.key), utf8(b.key));
        });
        return l;
    }

    static void checkAll(long t, String what) {
        Connection c = db.newConnection();
        if (t != Long.MAX_VALUE) c.setLookupTime(Time.units(t));
        long tq = t == Long.MAX_VALUE ? Long.MAX_VALUE : t;
        // Listing.
        List<String> exp = new ArrayList<>();
        for (String k : versions.keySet()) if (at(k, tq) != null) exp.add(k);
        exp.sort((a, b) -> cmpBytes(utf8(a), utf8(b)));
        List<String> got = new ArrayList<>();
        for (Kv<Object> kv : c.usePrimary(Object.class).dir("/p/").kvs()) {
            got.add(kv.key());
            Object ev = at(kv.key(), tq);
            if (ev instanceof String) {
                if (!(kv.value() instanceof byte[]) || !ev.equals(new String((byte[]) kv.value(), StandardCharsets.UTF_8))) fail(what + ": " + kv.key() + " is " + kv.value() + ", expected " + ev);
            } else if (!(kv.value() instanceof DbObject)) fail(what + ": " + kv.key() + " not an object");
        }
        if (!got.equals(exp)) fail(what + ": /p/ lists " + got.size() + ", expected " + exp.size());
        for (IndexDef d : defs) {
            boolean active = t == Long.MAX_VALUE ? d.activeTo == Long.MAX_VALUE : (t >= d.activeFrom && t < d.activeTo);
            if (!active) continue;
            checkIndex(c, d, tq, what);
        }
    }

    static boolean sameP(Person a, Person b) {
        return Objects.equals(a.name, b.name) && Objects.equals(a.age, b.age)
                && (a.score == null ? b.score == null : b.score != null && Double.compare(a.score, b.score) == 0)
                && Arrays.equals(a.tag, b.tag)
                && (a.addr == null ? b.addr == null : b.addr != null && Objects.equals(a.addr.city, b.addr.city) && a.addr.zip == b.addr.zip)
                && Arrays.equals(a.arr, b.arr);
    }

    static void compare(List<Entry> exp, Iterable<Kv<Person>> it, String what) {
        int i = 0;
        for (Kv<Person> kv : it) {
            if (i >= exp.size()) fail(what + ": more than " + exp.size() + " entries; extra " + kv.key());
            if (!kv.key().equals(exp.get(i).key)) fail(what + ": entry " + i + " is " + kv.key() + ", expected "
                    + exp.get(i).key + " (" + exp.size() + " expected)");
            if (!sameP(kv.value(), exp.get(i).p)) fail(what + ": entry " + i + " " + kv.key() + " has another value");
            i++;
        }
        if (i != exp.size()) fail(what + ": " + i + " entries, expected " + exp.size());
        nScans++;
    }

    static UseIndexBuilder<Person> eq(UseIndexBuilder<Person> b, String type, Object v) {
        switch (type) {
        case "long": return b.eq((Long) v);
        case "double": return b.eq((Double) v);
        case "string": return b.eq((String) v);
        default: return b.eq((byte[]) v);
        }
    }

    static UseIndexBuilder<Person> from(UseIndexBuilder<Person> b, String type, Object v, boolean incl) {
        switch (type) {
        case "long": return b.from((Long) v, incl);
        case "double": return b.from((Double) v, incl);
        case "string": return b.from((String) v, incl);
        default: return b.from((byte[]) v, incl);
        }
    }

    static UseIndexBuilder<Person> to(UseIndexBuilder<Person> b, String type, Object v, boolean incl) {
        switch (type) {
        case "long": return b.to((Long) v, incl);
        case "double": return b.to((Double) v, incl);
        case "string": return b.to((String) v, incl);
        default: return b.to((byte[]) v, incl);
        }
    }

    static boolean startsWith(Object v, Object pre) {
        if (v instanceof String) return ((String) v).startsWith((String) pre);
        byte[] a = (byte[]) v, p = (byte[]) pre;
        return a.length >= p.length && Arrays.equals(Arrays.copyOf(a, p.length), p);
    }

    static void checkIndex(Connection c, IndexDef d, long t, String what) {
        String w = what + ", index " + d.name + (t == Long.MAX_VALUE ? "" : " at " + t);
        List<Entry> all = entries(d, t);
        compare(all, c.useIndex(d.name, Person.class).kvs(), w + " forward");
        List<Entry> rev = new ArrayList<>(all);
        Collections.reverse(rev);
        compare(rev, c.useIndex(d.name, Person.class).backward().kvs(), w + " backward");
        if (all.isEmpty()) return;
        for (int q = 0; q < 6; q++) {
            Entry a = all.get(r.nextInt(all.size())), b = all.get(r.nextInt(all.size()));
            int lvl = d.types.length > 1 && r.nextBoolean() ? 1 : 0;
            if (lvl == 1) b = a;
            Object lo = a.lv[lvl], hi = b.lv[lvl];
            if (cmpLevel(lo, hi) > 0) { Object x = lo; lo = hi; hi = x; }
            boolean li = r.nextBoolean(), hiIncl = r.nextBoolean(), back = r.nextBoolean();
            int kind = r.nextInt(3);    // 0 from+to, 1 from only, 2 prefix
            String type = d.types[lvl];
            if (kind == 2 && !(type.equals("string") || type.equals("bytes"))) kind = 0;
            Object pre = null;
            if (kind == 2) {
                if (type.equals("string")) {
                    String s = (String) lo;
                    int[] cps = s.codePoints().toArray();
                    pre = new String(cps, 0, r.nextInt(cps.length + 1));
                } else {
                    byte[] bb = (byte[]) lo;
                    pre = Arrays.copyOf(bb, r.nextInt(bb.length + 1));
                }
            }
            List<Entry> exp = new ArrayList<>();
            for (Entry e : all) {
                if (lvl == 1 && cmpLevel(e.lv[0], a.lv[0]) != 0) continue;
                Object v = e.lv[lvl];
                if (kind == 2) { if (!startsWith(v, pre)) continue; }
                else {
                    int c1 = cmpLevel(v, lo);
                    if (c1 < 0 || (c1 == 0 && !li)) continue;
                    if (kind == 0) {
                        int c2 = cmpLevel(v, hi);
                        if (c2 > 0 || (c2 == 0 && !hiIncl)) continue;
                    }
                }
                exp.add(e);
            }
            if (back) Collections.reverse(exp);
            UseIndexBuilder<Person> ub = c.useIndex(d.name, Person.class);
            if (lvl == 1) ub = eq(ub, d.types[0], a.lv[0]);
            String desc;
            if (kind == 2) {
                ub = type.equals("string") ? ub.prefix((String) pre) : ub.prefix((byte[]) pre);
                desc = "prefix " + (pre instanceof String ? pre : Arrays.toString((byte[]) pre));
            } else {
                ub = from(ub, type, lo, li);
                desc = "from " + str(lo) + (li ? " incl" : " excl");
                if (kind == 0) { ub = to(ub, type, hi, hiIncl); desc += " to " + str(hi) + (hiIncl ? " incl" : " excl"); }
            }
            if (back) ub = ub.backward();
            compare(exp, ub.kvs(), w + " level " + (lvl + 1) + (lvl == 1 ? " eq " + str(a.lv[0]) : "") + " " + desc
                    + (back ? " backward" : ""));
        }
    }

    static String str(Object o) { return o instanceof byte[] ? Arrays.toString((byte[]) o) : String.valueOf(o); }

    static void checkOld(String what) {
        // A time among the versions' times.
        List<Long> ts = new ArrayList<>();
        for (TreeMap<Long, Object> v : versions.values()) synchronized (v) { ts.addAll(v.keySet()); }
        if (ts.isEmpty()) return;
        long t = ts.get(r.nextInt(ts.size()));
        if (r.nextBoolean()) t--;
        checkAll(t, what + " (old)");
        nOld++;
    }
}
