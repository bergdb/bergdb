import bergdb.core.Db;
import bergdb.core.Trans;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.pub.*;
import bergdb.pub.util.DbException;
import bergdb.stream.FileStream;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.util.*;

/**
 * App 3 of 024-26: release 2026.5's limits from a user's view, through the Pub API and the
 * Core API. Transactions near and over each limit (L1 operations, L2 key bytes, L3 keys'
 * bytes, L4 value bytes, L5 transaction bytes, L6 indexed levels), long Pub paths with "/"
 * counted twice and non-ASCII names. Every refusal must leave nothing written and the
 * database usable; an oracle of every key's value is checked after each step and after a
 * restart. Behaviour that the Javadoc leaves open is printed as "NOTE".
 *
 * Usage: java -Xmx3g -cp bergdb-release.jar:out Limits DIR
 */
public class Limits {
    static File dir;
    static Database db;
    static Connection c;
    /** The oracle: key -> expected value (byte[], String or Rec). */
    static final TreeMap<String, Object> model = new TreeMap<>();
    static final Set<String> dirs = new TreeSet<>();
    static int checks, refusals, notes;
    static final List<String> noteList = new ArrayList<>();

    public static class Rec {
        public String name;
        public long n;
        public byte[] data;
        public Rec() {}
        public Rec(String name, long n, byte[] data) { this.name = name; this.n = n; this.data = data; }
        @Override public boolean equals(Object o) {
            if (!(o instanceof Rec)) return false;
            Rec r = (Rec) o;
            return Objects.equals(name, r.name) && n == r.n && Arrays.equals(data, r.data);
        }
        @Override public String toString() { return "Rec(" + (name == null ? null : name.length() + " chars") + ", " + n + ")"; }
    }

    public static void main(String[] a) throws Exception {
        dir = new File(a[0]);
        Common.rmrf(dir);
        try {
            open(true);
            keyLengths();
            valueSizes();
            operations();
            indexedOperations();
            levels();
            keysBytes();
            transactionBytes();
            restart();
            verifyAll("after restart");
            db.close();
            core();
        } catch (Common.Fail f) {
            System.out.println("FAIL Limits: " + f.getMessage());
            try { db.close(); } catch (Throwable t) { }
            System.exit(1);
        } catch (Throwable t) {
            System.out.println("FAIL (exception) Limits: " + t);
            t.printStackTrace(System.out);
            try { db.close(); } catch (Throwable x) { }
            System.exit(2);
        }
        for (String n : noteList) System.out.println("NOTE " + n);
        Common.log("OK Limits: " + checks + " checks, " + refusals + " refusals checked, " + noteList.size() + " notes");
    }

    static void note(String s) { noteList.add(s); }

    static void open(boolean create) {
        DatabaseBuilder b = Factory.database();
        db = (create ? b.create(dir.getPath()) : b.open(dir.getPath())).start();
        c = db.connection();
    }

    static void restart() {
        db.close();
        open(false);
    }

    /** The stored length of a Pub key: its UTF-8 and one byte more for each '/'. */
    static int stored(String key) {
        int slashes = 0;
        for (char ch : key.toCharArray()) if (ch == '/') slashes++;
        return key.getBytes(StandardCharsets.UTF_8).length + slashes;
    }

    /** A key in directory d (as "/d/") with a name made of unit repeated, of stored length len. */
    static String keyOf(String d, String unit, int len, String suffix) {
        StringBuilder sb = new StringBuilder(d);
        String fill = "x";
        while (stored(sb + unit + suffix) <= len) sb.append(unit);
        while (stored(sb + suffix) < len) sb.append(fill);
        String k = sb + suffix;
        if (stored(k) != len) return null;
        return k;
    }

    static Throwable thrown(Runnable r) {
        try { r.run(); return null; } catch (Throwable t) { return t; }
    }

    static void expect(Class<? extends Throwable> cl, Throwable t, String what) {
        if (t == null) throw new Common.Fail(what + ": accepted, expected " + cl.getSimpleName());
        if (!cl.isInstance(t)) {
            t.printStackTrace(System.out);
            throw new Common.Fail(what + ": threw " + t + ", expected " + cl.getSimpleName());
        }
        refusals++;
    }

    static void ok(Throwable t, String what) {
        if (t != null) {
            t.printStackTrace(System.out);
            throw new Common.Fail(what + ": threw " + t);
        }
    }

    static String dirOf(String key) { return key.substring(0, key.lastIndexOf('/') + 1); }

    static void put(String key, Object v) {
        c.put(key, v);
        model.put(key, v);
        dirs.add(dirOf(key));
    }

    // ---- verification ----

    static Object getAs(Connection cn, String key, Object exp) {
        if (exp instanceof byte[]) return cn.get(key, byte[].class);
        if (exp instanceof String) return cn.get(key, String.class);
        return cn.get(key, Rec.class);
    }

    static boolean same(Object a, Object b) {
        if (a instanceof byte[] && b instanceof byte[]) return Arrays.equals((byte[]) a, (byte[]) b);
        return Objects.equals(a, b);
    }

    static void verifyKeys(Collection<String> keys, String what) {
        for (String k : keys) {
            Object exp = model.get(k);
            Object got = exp == null ? c.get(k, byte[].class) : getAs(c, k, exp);
            if (!same(exp, got)) throw new Common.Fail(what + ": key " + k + " (" + stored(k) + " bytes) got "
                    + show(got) + ", expected " + show(exp));
            checks++;
        }
    }

    static String show(Object o) {
        if (o instanceof byte[]) return "byte[" + ((byte[]) o).length + "]";
        if (o instanceof String) return "String(" + ((String) o).length() + ")";
        return String.valueOf(o);
    }

    static void verifyAll(String what) {
        verifyKeys(model.keySet(), what);
        // No key beyond the model's in the directories used.
        for (String d : dirs) {
            int n = 0;
            for (Kv<byte[]> kv : c.usePrimary(byte[].class).dir(d).kvs()) {
                if (!model.containsKey(kv.key())) throw new Common.Fail(what + ": extra key " + kv.key() + " in " + d);
                n++;
            }
            int exp = model.subMap(d, true, d + Character.MAX_VALUE, false).entrySet().stream()
                    .filter(e -> dirOf(e.getKey()).equals(d)).mapToInt(e -> 1).sum();
            if (n != exp) throw new Common.Fail(what + ": " + d + " lists " + n + " keys, expected " + exp);
            checks++;
        }
        verifyIndexes(what);
    }

    // ---- indexes: "byname" on /ix/ (string name); "byn" on /ix/ (long n) ----

    static boolean indexesMade;

    static void verifyIndexes(String what) {
        if (!indexesMade) return;
        List<String> exp = new ArrayList<>();
        TreeMap<String, List<String>> byName = new TreeMap<>(Comparator.comparing((String s) -> s.getBytes(StandardCharsets.UTF_8),
                Arrays::compareUnsigned));
        for (Map.Entry<String, Object> e : model.entrySet()) {
            if (!dirOf(e.getKey()).equals("/ix/") || !(e.getValue() instanceof Rec)) continue;
            Rec r = (Rec) e.getValue();
            if (r.name == null || r.name.getBytes(StandardCharsets.UTF_8).length + 1 > 111) continue;
            byName.computeIfAbsent(r.name, x -> new ArrayList<>()).add(e.getKey());
        }
        int n = 0;
        List<String> got = new ArrayList<>();
        for (Kv<Rec> kv : c.useIndex("byname", Rec.class).kvs()) {
            got.add(kv.value().name + "@" + kv.key());
            n++;
        }
        for (Map.Entry<String, List<String>> e : byName.entrySet())
            for (String k : e.getValue()) exp.add(e.getKey() + "@" + k);
        if (!got.equals(exp)) throw new Common.Fail(what + ": index byname lists " + got.size() + " entries, expected "
                + exp.size() + diff(got, exp));
        checks++;
    }

    static String diff(List<String> got, List<String> exp) {
        for (int i = 0; i < Math.min(got.size(), exp.size()); i++)
            if (!got.get(i).equals(exp.get(i))) return "; first difference at " + i + ": got " + abbrev(got.get(i))
                    + ", expected " + abbrev(exp.get(i));
        return "; lists agree for " + Math.min(got.size(), exp.size());
    }

    static String abbrev(String s) { return s.length() > 60 ? s.substring(0, 30) + "..." + s.substring(s.length() - 25) : s; }

    // ---- L2: keys ----

    static void keyLengths() {
        String[] units = {"a", "å", "€", "😀", "ab/", "\u0000", "\u0001"};
        String[] dirsUsed = {"/k/", "/kk/longer-directory-name/", "/kä/€/x/y/z/"};
        int n = 0;
        for (String d : dirsUsed) {
            for (String u : units) {
                for (int len = 105; len <= 113; len++) {
                    for (String suffix : new String[] {".bin", "", ".txt"}) {
                        String k = keyOf(d, u, len, suffix);
                        if (k == null || k.endsWith("/") || k.contains("//")) continue;
                        Object v = suffix.equals(".txt") ? "v" + len : suffix.isEmpty() ? new Rec("r", len, null) : new byte[] {(byte) len};
                        n++;
                        if (len <= 111) {
                            ok(thrown(() -> put(k, v)), "put of a key of " + len + " bytes " + k);
                            final int flen = len;
                            ok(thrown(() -> verifyKeys(List.of(k), "key " + flen)), "get " + k);
                        } else {
                            expect(IllegalArgumentException.class, thrown(() -> c.put(k, v)), "put of a key of " + len + " bytes " + k);
                            expect(IllegalArgumentException.class, thrown(() -> c.w().put(k, v)), "w().put of a key of " + len + " bytes");
                            expect(IllegalArgumentException.class, thrown(() -> c.delete(k)), "delete of a key of " + len + " bytes");
                            expect(IllegalArgumentException.class, thrown(() -> c.w().delete(k)), "w().delete of a key of " + len + " bytes");
                            expect(IllegalArgumentException.class, thrown(() -> c.rw(env -> env.put(k, v))), "rw put of a key of " + len);
                            // A get of a key over the limit: the Javadoc does not say.
                            Throwable g = thrown(() -> c.get(k, byte[].class));
                            noteOnce("get of a key of 112+ bytes: " + (g == null ? "returns null" : g.getClass().getSimpleName()));
                            Throwable ex = thrown(() -> c.exists(k));
                            noteOnce("exists() of a key of 112+ bytes: " + (ex == null ? "returns false" : ex.getClass().getSimpleName()));
                        }
                    }
                }
            }
        }
        // A w() with a refused put: the builder after the refusal. Since 024-27 (024-26, U26-5, decided) a
        // refused call spoils the builder: its later calls and execute() throw, and nothing is written
        // (028-23: until then the app noted what it saw, the builder going on).
        WBuilder w = c.w();
        w.put("/k/ok1.bin", new byte[] {1});
        String longKey = keyOf("/k/", "a", 112, ".bin");
        expect(IllegalArgumentException.class, thrown(() -> w.put(longKey, new byte[] {2})), "w().put of a 112-byte key");
        expect(IllegalStateException.class, thrown(() -> w.put("/k/ok2.bin", new byte[] {3})), "put() on a spoiled WBuilder");
        expect(IllegalStateException.class, thrown(() -> w.execute()), "execute() of a spoiled WBuilder");
        if (c.get("/k/ok1.bin", byte[].class) != null || c.get("/k/ok2.bin", byte[].class) != null)
            throw new Common.Fail("a spoiled WBuilder wrote a put");
        // Deep directories: each '/' counts two.
        StringBuilder deep = new StringBuilder();
        while (stored(deep + "/d") + 2 <= 109) deep.append("/d");
        String deepKey = deep + "/x";
        ok(thrown(() -> put(deepKey, "deep")), "put of a deep key of " + stored(deepKey) + " bytes");
        String deeper = deep + "/d/x";
        if (stored(deeper) > 111) expect(IllegalArgumentException.class, thrown(() -> c.put(deeper, "x")), "deep key of " + stored(deeper));
        // Key replace: "${transactionTime}" (18 chars) becomes 18 digits.
        c.setEnableKeyReplace(true);
        String tmpl = keyOf("/kr/", "q", 111 - 18, "") + "${transactionTime}";
        Throwable tr = thrown(() -> {
            Transaction tx = c.put(tmpl, "replaced");
            String real = tmpl.replace("${transactionTime}", String.format("%018d", tx.getTime().units()));
            model.put(real, "replaced");
            dirs.add("/kr/");
        });
        ok(tr, "key replace at 111 bytes");
        c.setEnableKeyReplace(false);
        verifyAll("keys");
        Common.log("keys: " + n + " keys tried");
    }

    static final Set<String> notesSeen = new HashSet<>();
    static void noteOnce(String s) { if (notesSeen.add(s)) note(s); }

    // ---- L4: values ----

    static void valueSizes() {
        int max = 8 * 1024 * 1024;
        byte[] big = new byte[max];
        new Random(4).nextBytes(big);
        ok(thrown(() -> put("/v/max.bin", big)), "put of a value of 8 MiB");
        byte[] over = Arrays.copyOf(big, max + 1);
        expect(IllegalArgumentException.class, thrown(() -> c.put("/v/over.bin", over)), "put of 8 MiB + 1");
        expect(IllegalArgumentException.class, thrown(() -> c.w().put("/v/over.bin", over)), "w().put of 8 MiB + 1");
        expect(IllegalArgumentException.class, thrown(() -> c.rw(env -> env.put("/v/over.bin", over))), "rw put of 8 MiB + 1");
        // A String: 8 MiB of UTF-8 exactly, then one byte more by an 'å'.
        char[] cs = new char[max];
        Arrays.fill(cs, 'z');
        String s8 = new String(cs);
        ok(thrown(() -> put("/v/max.txt", s8)), "put of a String of 8 MiB UTF-8");
        String s9 = new String(cs, 0, max - 1) + "å";
        expect(IllegalArgumentException.class, thrown(() -> c.put("/v/over.txt", s9)), "put of a String of 8 MiB + 1 UTF-8");
        // An object near 8 MiB: find the largest byte[] field that is taken.
        int lo = max - 200, hi = max;
        Throwable last = null;
        int largest = -1;
        for (int len = lo; len <= hi; len += 1) {
            byte[] d = Arrays.copyOf(big, len);
            Rec r = new Rec("big", 1, d);
            Throwable t = thrown(() -> c.put("/v/obj", r));
            if (t == null) { largest = len; model.put("/v/obj", r); dirs.add("/v/"); }
            else {
                if (!(t instanceof IllegalArgumentException)) throw new Common.Fail("object put of " + len + ": " + t);
                last = t;
                break;
            }
        }
        if (largest < 0) throw new Common.Fail("no object near 8 MiB taken");
        note("an object Rec(name \"big\", n 1, data byte[" + largest + "]) is the largest taken: its overhead is "
                + (max - largest) + " bytes; refused with: " + (last == null ? "-" : last.getMessage()));
        verifyAll("values");
        Common.log("values: largest object field " + largest);
    }

    // ---- L1: operations ----

    static void operations() {
        // 500 puts: taken. 501: refused at execute, nothing written.
        WBuilder w = c.w();
        Map<String, Object> m = new LinkedHashMap<>();
        for (int i = 0; i < 500; i++) { w.put("/o/" + i + ".bin", new byte[] {(byte) i}); m.put("/o/" + i + ".bin", new byte[] {(byte) i}); }
        ok(thrown(w::execute), "w() of 500 puts");
        model.putAll(m);
        dirs.add("/o/");
        WBuilder w2 = c.w();
        for (int i = 0; i < 501; i++) w2.put("/o/" + i + ".bin", new byte[] {7});
        expect(DbException.class, thrown(w2::execute), "w() of 501 puts");
        verifyAll("501 puts");
        // 600 puts of one key: one operation.
        WBuilder w3 = c.w();
        for (int i = 0; i < 600; i++) w3.put("/o/same.bin", new byte[] {(byte) i});
        ok(thrown(w3::execute), "w() of 600 puts of one key");
        model.put("/o/same.bin", new byte[] {(byte) 599});
        // 500 puts + 1 delete of an absent key: is the delete an operation?
        WBuilder w4 = c.w();
        for (int i = 0; i < 500; i++) w4.put("/o/" + i + ".bin", new byte[] {9});
        w4.delete("/o/absent.bin");
        Throwable t4 = thrown(w4::execute);
        if (t4 == null) { for (int i = 0; i < 500; i++) model.put("/o/" + i + ".bin", new byte[] {9}); }
        else if (!(t4 instanceof DbException)) throw new Common.Fail("500 puts + delete of absent: " + t4);
        note("500 puts and a delete of a key without a value: " + (t4 == null ? "taken" : "refused (the delete counts)"));
        // rw() of 501 puts: refused, nothing written.
        expect(DbException.class, thrown(() -> c.rw(env -> { for (int i = 0; i < 501; i++) env.put("/o/rw" + i + ".bin", new byte[] {1}); })),
                "rw() of 501 puts");
        // 250 deletes + 251 puts.
        WBuilder w5 = c.w();
        for (int i = 0; i < 250; i++) w5.delete("/o/" + i + ".bin");
        for (int i = 0; i < 251; i++) w5.put("/o/n" + i + ".bin", new byte[] {1});
        expect(DbException.class, thrown(w5::execute), "250 deletes and 251 puts");
        verifyAll("operations");
        Common.log("operations done");
    }

    static void indexedOperations() {
        db.indexBuilder("byname").dir("/ix/").type("string").field("name").start().join();
        indexesMade = true;
        dirs.add("/ix/");
        // New objects in a directory with one index.
        int newTaken = probeNew("/ix/a", 160, 260);
        note("new objects in a directory with one index: " + newTaken + " taken in one w(), " + (newTaken + 1) + " refused");
        verifyAll("new objects");
        // Overwrites that change the indexed field: 1 + 2k = 3 each.
        int over = probeOverwrite("/ix/a", newTaken, true);
        note("overwrites that change the indexed field, one index: " + over + " taken, " + (over + 1) + " refused (doc: 166)");
        int same = probeOverwrite("/ix/a", newTaken, false);
        note("overwrites that keep the indexed field, one index: " + same + " taken");
        verifyAll("indexed operations");
        Common.log("indexed operations: new " + newTaken + ", changing " + over + ", same " + same);
    }

    /** The largest count of new objects in one w() that is taken, from lo; checks every refusal. */
    static int probeNew(String prefix, int lo, int hi) {
        int taken = -1;
        for (int n = lo; n <= hi; n++) {
            WBuilder w = c.w();
            Map<String, Object> m = new LinkedHashMap<>();
            for (int i = 0; i < n; i++) { String k = prefix + "-" + n + "-" + i; Rec r = new Rec("nm" + (i % 50), i, null); w.put(k, r); m.put(k, r); }
            Throwable t = thrown(w::execute);
            if (t == null) { model.putAll(m); taken = n; }
            else {
                expect(DbException.class, t, "new objects " + n);
                verifyKeys(m.keySet(), "refused new objects " + n);
                break;
            }
        }
        return taken;
    }

    static int probeOverwrite(String prefix, int n0, boolean change) {
        List<String> keys = new ArrayList<>();
        for (int i = 0; i < n0; i++) keys.add(prefix + "-" + n0 + "-" + i);
        int taken = -1;
        for (int n = 100; n <= Math.min(n0, 501); n++) {
            WBuilder w = c.w();
            Map<String, Object> m = new LinkedHashMap<>();
            for (int i = 0; i < n; i++) {
                Rec old = (Rec) model.get(keys.get(i));
                Rec r = new Rec(change ? "c" + n + "-" + (i % 50) : old.name, old.n + 1, null);
                w.put(keys.get(i), r);
                m.put(keys.get(i), r);
            }
            Throwable t = thrown(w::execute);
            if (t == null) { model.putAll(m); taken = n; }
            else {
                expect(DbException.class, t, "overwrites " + n);
                verifyKeys(m.keySet(), "refused overwrites " + n);
                break;
            }
        }
        return taken;
    }

    // ---- L6: indexed levels ----

    static void levels() {
        String[] units = {"a", "å", "€", "😀", "\u0000", "\u0001"};
        for (String u : units) {
            for (int bytes = 105; bytes <= 112; bytes++) {
                StringBuilder sb = new StringBuilder();
                while (sb.toString().getBytes(StandardCharsets.UTF_8).length + u.getBytes(StandardCharsets.UTF_8).length <= bytes) sb.append(u);
                while (sb.toString().getBytes(StandardCharsets.UTF_8).length < bytes) sb.append('a');
                String name = sb.toString();
                int levelBytes = name.getBytes(StandardCharsets.UTF_8).length + 1;
                String key = "/ix/l-" + u.codePointAt(0) + "-" + bytes;
                Object before = model.get(key);
                Rec r = new Rec(name, bytes, null);
                if (u.charAt(0) < 2) {
                    // U+0000 and U+0001: the Javadoc counts a string level as its UTF-8 and a byte.
                    Throwable t = thrown(() -> put(key, r));
                    if (t != null) {
                        model.remove(key);
                        if (before != null) model.put(key, before);
                        expect(IllegalArgumentException.class, t, "control level " + levelBytes);
                        verifyKeys(List.of(key), "refused control level");
                        noteOnce("a string level of U+" + String.format("%04X", (int) u.charAt(0)) + " chars: refused at "
                                + bytes + " UTF-8 bytes (" + levelBytes + " by the Javadoc's count): such a char takes two bytes in a level");
                    }
                } else if (levelBytes <= 111) {
                    ok(thrown(() -> put(key, r)), "put of an object with a level of " + levelBytes + " bytes");
                } else {
                    expect(IllegalArgumentException.class, thrown(() -> c.put(key, r)), "put, level of " + levelBytes);
                    expect(IllegalArgumentException.class, thrown(() -> c.w().put(key, r).execute()), "w(), level of " + levelBytes);
                    expect(IllegalArgumentException.class, thrown(() -> c.rw(env -> env.put(key, r))), "rw(), level of " + levelBytes);
                    verifyKeys(List.of(key), "refused level " + levelBytes);
                    // An existing object at the key, then an overwrite with a long level.
                    Rec small = new Rec("small" + bytes, bytes, null);
                    put(key, small);
                    expect(IllegalArgumentException.class, thrown(() -> c.put(key, r)), "overwrite, level of " + levelBytes);
                    verifyKeys(List.of(key), "refused overwrite level " + levelBytes);
                }
            }
        }
        verifyAll("levels");
        // A w() with one bad object among good ones: nothing of it written.
        WBuilder w = c.w();
        Map<String, Object> m = new LinkedHashMap<>();
        for (int i = 0; i < 10; i++) { Rec r = new Rec("good" + i, i, null); w.put("/ix/mix" + i, r); m.put("/ix/mix" + i, r); }
        char[] longName = new char[120];
        Arrays.fill(longName, 'L');
        w.put("/ix/mixbad", new Rec(new String(longName), 0, null));
        expect(IllegalArgumentException.class, thrown(w::execute), "w() with one long level among 10");
        verifyKeys(m.keySet(), "w() with one bad level");
        verifyKeys(List.of("/ix/mixbad"), "w() with one bad level");
        // Objects with long levels put before an index: the build gives them no entry.
        for (int i = 0; i < 5; i++) put("/iy/long" + i, new Rec(new String(longName) + i, i, null));
        for (int i = 0; i < 5; i++) put("/iy/short" + i, new Rec("s" + i, i, null));
        Throwable bt = thrown(() -> db.indexBuilder("iyname").dir("/iy/").type("string").field("name").start().join());
        ok(bt, "build of an index over objects with long levels");
        int cnt = 0;
        for (Rec r : c.useIndex("iyname", Rec.class).objects()) {
            if (r.name.length() > 100) throw new Common.Fail("index iyname lists an object with a long level");
            cnt++;
        }
        Common.check(cnt == 5, "index iyname lists " + cnt + ", expected 5");
        // A bytes level: what does it take?
        Throwable bb = thrown(() -> db.indexBuilder("izb").dir("/iz/").type("bytes").field("data").start().join());
        ok(bb, "build of a bytes index");
        for (int fill : new int[] {0x00, 0x01, 0x41, 0xff}) {
            int largestBytes = -1;
            for (int len = 1; len <= 112; len++) {
                byte[] d = new byte[len];
                Arrays.fill(d, (byte) fill);
                Rec r = new Rec("b", len, d);
                Throwable t = thrown(() -> c.put("/iz/b", r));
                if (t == null) { model.put("/iz/b", r); dirs.add("/iz/"); largestBytes = len; }
                else if (!(t instanceof IllegalArgumentException)) throw new Common.Fail("bytes level " + len + ": " + t);
                else verifyKeys(List.of("/iz/b"), "bytes level refused");
            }
            note("a bytes level of bytes 0x" + Integer.toHexString(fill) + ": the largest byte[] taken is " + largestBytes
                    + " bytes (the Javadoc gives the size of string, long and double levels only)");
        }
        // Two levels: string + long.
        db.indexBuilder("namen").dir("/ix/").type("string").field("name").type("long").field("n").start().join();
        int largestTwo = -1;
        for (int len = 98; len <= 105; len++) {
            char[] cs = new char[len];
            Arrays.fill(cs, 'w');
            Rec r = new Rec(new String(cs), len, null);
            Throwable t = thrown(() -> c.put("/ix/two", r));
            if (t == null) { model.put("/ix/two", r); largestTwo = len; }
            else if (!(t instanceof IllegalArgumentException)) throw new Common.Fail("two levels " + len + ": " + t);
            else verifyKeys(List.of("/ix/two"), "two levels refused");
        }
        note("levels string + long: the longest ASCII name taken is " + largestTwo + " (1 + " + largestTwo + " + 8 = "
                + (largestTwo + 9) + " bytes; but byname, one level, takes up to 110 chars on the same put)");
        verifyAll("levels 2");
        Common.log("levels done");
    }

    // ---- L3: keys' bytes ----

    static void keysBytes() {
        // Overwrites in /ix/ of objects with long keys and long names: each makes three keys of
        // the transaction (its key, the old entry deleted, the new one put) in each of two indexes.
        int made = 0;
        List<String> keys = new ArrayList<>();
        for (int i = 0; i < 120; i++) {
            String k = keyOf("/ix/", "K", 100, "") ;
            k = k.substring(0, k.length() - 4) + String.format("%04d", i);
            keys.add(k);
            char[] cs = new char[95];
            Arrays.fill(cs, (char) ('a' + i % 26));
            Rec r = new Rec(new String(cs), i, null);
            put(k, r);
            made++;
        }
        int taken = -1;
        for (int n = 20; n <= 120; n++) {
            WBuilder w = c.w();
            Map<String, Object> m = new LinkedHashMap<>();
            for (int i = 0; i < n; i++) {
                Rec old = (Rec) model.get(keys.get(i));
                String nm = (old.name.charAt(0) == 'Z' ? 'Y' : 'Z') + old.name.substring(1);
                Rec r = new Rec(nm, old.n, null);
                w.put(keys.get(i), r);
                m.put(keys.get(i), r);
            }
            Throwable t = thrown(w::execute);
            if (t == null) { model.putAll(m); taken = n; }
            else {
                expect(DbException.class, t, "overwrites of long objects " + n);
                note("overwrites of objects with 100-byte keys and 95-char names in a directory with indexes byname and"
                        + " namen: " + taken + " taken, " + n + " refused (" + (n * 5) + " operations): " + t.getMessage());
                verifyKeys(m.keySet(), "refused long overwrites " + n);
                break;
            }
        }
        verifyAll("keys bytes");
        Common.log("keys bytes: " + made + " objects, " + taken + " overwrites taken");
    }

    // ---- L5: transaction bytes ----

    static void transactionBytes() {
        long max = 32L * 1024 * 1024;
        int v8 = 8 * 1024 * 1024;
        String[] ks = {"/t/a.bin", "/t/b.bin", "/t/c.bin", "/t/d.bin"};
        long keys = 0;
        for (String k : ks) keys += stored(k);
        // Exactly 32 MiB of keys and values, as the package's Limits count them.
        int last = (int) (max - keys - 3L * v8);
        Throwable t = tryBytes(ks, v8, last);
        if (t == null) note("L5: 3 x 8 MiB + " + last + " bytes with keys of " + keys + " bytes (32 MiB exactly): taken");
        else {
            if (!(t instanceof DbException)) throw new Common.Fail("L5 exact: " + t);
            // find the largest taken
            int lo = last - 4096, hi = last;
            int best = -1;
            for (int x = hi; x >= lo; x -= 1) {
                if (tryBytes(ks, v8, x) == null) { best = x; break; }
            }
            note("L5: 32 MiB of keys and values as the Javadoc counts them is refused (" + t.getMessage() + "); the largest taken is "
                    + (best < 0 ? "below" : "" + (max - keys - 3L * v8 - best) + " bytes less"));
        }
        Throwable t2 = tryBytes(ks, v8, last + 1);
        expect(DbException.class, t2, "L5: one byte over 32 MiB");
        verifyAll("transaction bytes");
        Common.log("transaction bytes done");
    }

    static Throwable tryBytes(String[] ks, int v8, int lastLen) {
        WBuilder w = c.w();
        Map<String, Object> m = new LinkedHashMap<>();
        Random r = new Random(lastLen);
        for (int i = 0; i < 4; i++) {
            byte[] v = new byte[i < 3 ? v8 : lastLen];
            r.nextBytes(v);
            w.put(ks[i], v);
            m.put(ks[i], v);
        }
        Throwable t = thrown(w::execute);
        if (t == null) { model.putAll(m); dirs.add("/t/"); }
        else verifyKeys(m.keySet(), "refused L5 " + lastLen);
        return t;
    }

    // ---- the Core API ----

    static void core() throws Exception {
        File cd = new File(dir.getPath() + "-core");
        Common.rmrf(cd);
        Common.Model cm = new Common.Model();
        try (Db d = Db.builder().mainStream(new FileStream(cd, false)).start()) {
            byte[] k111 = new byte[111];
            Arrays.fill(k111, (byte) 0x33);
            byte[] k112 = new byte[112];
            Arrays.fill(k112, (byte) 0x33);
            Common.exec(d, cm, Map.of(new Common.K(k111), new byte[] {1}));
            expect(IllegalArgumentException.class, thrown(() -> d.trans().put(k112, new byte[] {1})), "Core put of 112 bytes");
            expect(IllegalArgumentException.class, thrown(() -> d.trans().put(Keys.toSegments(k112), new byte[] {1})), "Core put(long[]) of 112");
            Throwable dt = thrown(() -> d.trans().delete(k112));
            if (dt == null) note("Core: Trans.Builder.delete(byte[]) of a key of 112 bytes is taken by the call");
            else if (dt instanceof IllegalArgumentException) refusals++;
            Throwable dt2 = thrown(() -> d.trans().delete(Keys.toSegments(k112)));
            if (dt2 == null) note("Core: Trans.Builder.delete(long[]) of a key of 112 bytes is taken by the call");
            Throwable kr = thrown(() -> d.trans().keyRead(Keys.toSegments(k112)));
            note("Core: keyRead of a key of 112 bytes: " + (kr == null ? "taken" : kr.toString()));
            // A delete of a 112-byte key, executed: what happens?
            if (dt == null) {
                long len0 = d.getStreamLength();
                Throwable et = thrown(() -> d.execute(d.trans().delete(k112).build()));
                note("Core: execute() of a delete of a key of 112 bytes: " + (et == null ? "taken, stream grew by "
                        + (d.getStreamLength() - len0) : et.toString()));
            }
            // A String key whose bkey is 112 bytes.
            StringBuilder sb = new StringBuilder();
            while (Keys.toBytes(sb.toString() + "a").length <= 112) sb.append('a');
            String sk = sb.toString();
            Throwable st = thrown(() -> d.trans().put(sk, "v"));
            note("Core: put(String) whose bkey is " + Keys.toBytes(sk).length + " bytes: " + (st == null ? "taken" : st.getClass().getSimpleName()));
            // Values.
            byte[] v8 = new byte[Db.MAX_VALUE_BYTES];
            Common.exec(d, cm, Map.of(new Common.K(new byte[] {0x40}), v8));
            expect(IllegalArgumentException.class, thrown(() -> d.trans().put(new byte[] {0x41}, new byte[Db.MAX_VALUE_BYTES + 1])), "Core value over L4");
            // L1.
            Trans.Builder b = d.trans();
            for (int i = 0; i < 501; i++) b.put(new byte[] {0x50, (byte) (i >> 8), (byte) i}, new byte[] {1});
            long len0 = d.getStreamLength();
            long tc0 = d.getTransactionCount();
            expect(DbException.class, thrown(() -> d.execute(b.build())), "Core 501 operations");
            Common.check(d.getStreamLength() == len0 && d.getTransactionCount() == tc0, "Core: refused L1 wrote");
            // L5 exactly, in the Core: keys + values.
            long max = Db.MAX_TRANS_BYTES;
            byte[][] ks = {{0x60}, {0x61}, {0x62}, {0x63}};
            int lastLen = (int) (max - 4 - 3L * Db.MAX_VALUE_BYTES);
            Throwable l5 = thrown(() -> {
                Map<Common.K, byte[]> ops = new LinkedHashMap<>();
                for (int i = 0; i < 4; i++) ops.put(new Common.K(ks[i]), new byte[i < 3 ? Db.MAX_VALUE_BYTES : lastLen]);
                Common.exec(d, cm, ops);
            });
            note("Core L5 at exactly 32 MiB of keys and values: " + (l5 == null ? "taken" : l5.toString()));
            Throwable l5b = thrown(() -> {
                Map<Common.K, byte[]> ops = new LinkedHashMap<>();
                for (int i = 0; i < 4; i++) ops.put(new Common.K(ks[i]), new byte[i < 3 ? Db.MAX_VALUE_BYTES : lastLen + 1]);
                Common.exec(d, cm, ops);
            });
            expect(DbException.class, l5b, "Core L5 one byte over");
            // A key transformation that makes a key longer than 111 bytes.
            Throwable kt = thrown(() -> {
                Trans.Builder tb = d.trans();
                tb.put(Keys.toSegments(new byte[] {0x70}), (tr, i) -> {
                    tr.kvs[i].setKey(Keys.toSegments(k112));
                    tr.writeKeyHashes[i] = Keys.hash(tr.kvs[i].getKey());
                }, new byte[] {1}, null);
                d.execute(tb.build());
            });
            note("Core: a key transformation that gives a key of 112 bytes: " + (kt == null ? "taken" : kt.toString()));
            // Builder rules of 2026.5: the last call on a key wins; a key transformation onto another KV's key is refused.
            byte[] kA = {0x71, 1}, kB = {0x71, 2};
            Common.exec(d, cm, Map.of(new Common.K(kA), new byte[] {1}, new Common.K(kB), new byte[] {2}));
            Trans t1 = d.trans().put(kA, new byte[] {3}).delete(kA).delete(kB).put(kB, new byte[] {4}).build();
            d.execute(t1);
            Map<Common.K, byte[]> m1 = new LinkedHashMap<>();
            m1.put(new Common.K(kA), Common.DELETED);
            m1.put(new Common.K(kB), new byte[] {4});
            cm.apply(m1, t1.tt);
            Common.verifyFull(d, cm, Long.MAX_VALUE, "core: last call wins");
            long len1 = d.getStreamLength();
            Throwable kt2 = thrown(() -> {
                Trans.Builder tb = d.trans();
                tb.put(Keys.toSegments(new byte[] {0x72}), (tr, i) -> {
                    tr.kvs[i].setKey(Keys.toSegments(kB));
                    tr.writeKeyHashes[i] = Keys.hash(tr.kvs[i].getKey());
                }, new byte[] {9}, null);
                tb.delete(kB);
                d.execute(tb.build());
            });
            expect(DbException.class, kt2, "Core: a key transformation onto a key the transaction deletes");
            Common.check(d.getStreamLength() == len1, "Core: refused KT transaction wrote");
            Throwable kt3 = thrown(() -> {
                Trans.Builder tb = d.trans();
                tb.put(Keys.toSegments(new byte[] {0x72}), (tr, i) -> {
                    tr.kvs[i].setKey(Keys.toSegments(k111));
                    tr.writeKeyHashes[i] = Keys.hash(tr.kvs[i].getKey());
                }, new byte[] {9}, null);
                Trans tx = tb.build();
                d.execute(tx);
                cm.apply(Map.of(new Common.K(k111), new byte[] {9}), tx.tt);
            });
            ok(kt3, "Core: a key transformation that gives a key of 111 bytes");
            Common.verifyFull(d, cm, Long.MAX_VALUE, "core");
        }
        try (Db d = Db.builder().mainStream(new FileStream(cd, false)).start()) {
            Common.verifyFull(d, cm, Long.MAX_VALUE, "core after restart");
        }
        Common.log("core done");
    }
}
