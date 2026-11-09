package bergdb.pubimp;

import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NavigableMap;
import java.util.NoSuchElementException;
import java.util.Random;
import java.util.TreeMap;

import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.Action;
import bergdb.pub.Connection;
import bergdb.pub.DataFormatException;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.Kv;
import bergdb.pub.ObjectCreationException;
import bergdb.pub.RwEnvironment;
import bergdb.pub.TestClock;
import bergdb.pub.Time;
import bergdb.pub.UsePrimaryBuilder;
import bergdb.pub.WBuilder;
import bergdb.stream.MemoryStream;

/**
 * Harness H4 of release 2026.4: the primary scan, Connection.usePrimary() (bergdb 020-10,
 * sections 3.5, 3.6 and 9.4; 020-01, section 15). Random puts and deletes of String, byte[]
 * and object values, in w() and rw(), in a directory, its subdirectory, the root and the
 * directory's neighbours, with restarts; and listings of a directory at a lookup time (a
 * past one, the latest, or a frozen one), with startAt(), inclusive() and backward(), as
 * byte[], Object, String, DbObject and a class, with objects() and kvs(), each iterated
 * once or twice. Every listing must equal the one computed from a simple reference: each
 * key's versions by time (harness 6.7's, bergdb 018-04) and section 3.5's table of what
 * each type lists. The reference is written apart from the code: it orders names by their
 * code points (their UTF-8 bytes) and compares Java values, not keys or stored bytes.
 *
 * <p>Each run has a seed, printed at a failure, so that it can be repeated:
 * {@code main(SEED)} or {@code run(seed, steps)}.</p>
 *
 * @author Frans Lundberg
 */
public class PrimaryHarness {

    /** The class of the objects: a Data Object class (bergdb 020-09). */
    public static class Item {
        public int n;
        public String s;

        public Item() {
        }

        public Item(int n, String s) {
            this.n = n;
            this.s = s;
        }
    }

    /**
     * The directories written: the one listed most, its subdirectory, the root, and two
     * whose names start with the first's.
     */
    static final String[] DIRS = {"/h/", "/h/sub/", "/", "/h0/", "/h-/"};

    /**
     * The names: every kind of suffix (an object key has none or ".obj"), names that start
     * as the key encoding's prefixes ('-' a file, 'd' a directory), a name that is a
     * directory's ("h"), and names whose code-point order differs from their UTF-16 order
     * (U+FF5E sorts before U+1F600).
     */
    static final String[] NAMES = {"a", "a b", "a.txt", "a.obj", "a.bin", "ab", "b", "-x", "dx",
            "x.", ".h", "h", "h0", "å", "€.txt", "～", "😀",
            "😀.txt", "z"};

    /** Names of the bulk writes, which make a listing take several of the scan's pages. */
    static final int BULK = 250;

    /** Names to start at that no write uses: before, between and after the others. */
    static final String[] OTHER_STARTS = {"0", "a0", "c", "n", "n1", "n100x", "zz", "￿",
            "😁"};

    /** The types listed: byte[], Object, String, DbObject and a class. */
    static final Class<?>[] TYPES = {byte[].class, Object.class, String.class, DbObject.class,
            Item.class};

    // ======== The reference ========

    /** A value: a String, a byte[] or an object (an Item). */
    static final class Val {
        final String string;
        final byte[] bytes;
        final Item item;

        Val(String string, byte[] bytes, Item item) {
            this.string = string;
            this.bytes = bytes;
            this.item = item;
        }

        boolean isObject() {
            return item != null;
        }

        /** The stored bytes of a String or a byte[]. */
        byte[] stored() {
            return string != null ? string.getBytes(StandardCharsets.UTF_8) : bytes;
        }

        /** The value to put. */
        Object toPut() {
            return string != null ? string : bytes != null ? bytes : item;
        }

        public String toString() {
            if (string != null) {
                return "String \"" + show(string) + "\"";
            } else if (bytes != null) {
                return "byte[] " + Arrays.toString(bytes);
            } else {
                return "Item(" + item.n + ", \"" + show(item.s) + "\")";
            }
        }
    }

    /** Names in code-point order, which is their UTF-8 bytes' unsigned order. */
    static final Comparator<String> NAME_ORDER = new Comparator<String>() {
        public int compare(String a, String b) {
            byte[] x = a.getBytes(StandardCharsets.UTF_8);
            byte[] y = b.getBytes(StandardCharsets.UTF_8);
            for (int i = 0; i < Math.min(x.length, y.length); i++) {
                int d = (x[i] & 0xff) - (y[i] & 0xff);
                if (d != 0) {
                    return d;
                }
            }
            return x.length - y.length;
        }
    };

    /** Each key's versions by time; a delete's value is null. */
    final TreeMap<String, TreeMap<Long, Val>> versions = new TreeMap<String, TreeMap<Long, Val>>();

    /** The times of the transactions, in order. */
    final List<Long> times = new ArrayList<Long>();

    void commit(long time, List<String> keys, List<Val> values) {
        if (!times.isEmpty() && time <= times.get(times.size() - 1)) {
            throw new AssertionError("transaction time " + time + " not after the last, "
                    + times.get(times.size() - 1));
        }
        times.add(time);
        for (int i = 0; i < keys.size(); i++) {         // the last call on a key wins
            TreeMap<Long, Val> v = versions.get(keys.get(i));
            if (v == null) {
                v = new TreeMap<Long, Val>();
                versions.put(keys.get(i), v);
            }
            v.put(time, values.get(i));
        }
    }

    /**
     * An object key: no suffix, or ".obj" (Entries.isObjectKey, written again): the suffix
     * follows the last '.' of the key's last part, a '.' in a directory's name is not one.
     */
    static boolean isObjectKey(String key) {
        int i = key.lastIndexOf('.');
        String suffix = i <= key.lastIndexOf('/') ? "" : key.substring(i + 1);
        return suffix.isEmpty() || suffix.equals("obj");
    }

    /**
     * The listing of dir at time t, by section 3.5: the directory's own keys with a value at
     * t, in name order, from startAt if not null, backward or not, of type's kind.
     */
    List<Map.Entry<String, Val>> expected(String dir, long t, String startAt, boolean inclusive,
            boolean backward, Class<?> type) {
        TreeMap<String, Val> byName = new TreeMap<String, Val>(NAME_ORDER);
        for (Map.Entry<String, TreeMap<Long, Val>> e : versions.entrySet()) {
            String key = e.getKey();
            int slash = key.lastIndexOf('/');
            if (!key.substring(0, slash + 1).equals(dir)) {
                continue;
            }
            Map.Entry<Long, Val> v = e.getValue().floorEntry(t);
            if (v != null && v.getValue() != null) {
                byName.put(key.substring(slash + 1), v.getValue());
            }
        }
        NavigableMap<String, Val> range = byName;
        if (startAt != null) {
            range = backward ? byName.headMap(startAt, inclusive)
                    : byName.tailMap(startAt, inclusive);
        }
        if (backward) {
            range = range.descendingMap();
        }
        List<Map.Entry<String, Val>> result = new ArrayList<Map.Entry<String, Val>>();
        for (Map.Entry<String, Val> e : range.entrySet()) {
            boolean object = e.getValue().isObject();
            boolean listed = type == byte[].class || type == Object.class
                    || (type == String.class ? !object : object);
            if (listed) {
                result.add(new java.util.AbstractMap.SimpleEntry<String, Val>(dir + e.getKey(),
                        e.getValue()));
            }
        }
        return result;
    }

    /**
     * Checks a listed value against the reference's: section 3.5's table, each as get()
     * gives it.
     */
    static void checkValue(String what, Class<?> type, String key, Val expected, Object actual) {
        if (actual == null) {
            throw new AssertionError(what + ": null for " + expected);
        }
        if (type == byte[].class) {
            if (expected.isObject()) {
                checkItem(what, expected.item, new DbObject((byte[]) actual));
            } else {
                checkBytes(what, expected.stored(), actual);
            }
        } else if (type == Object.class) {
            if (expected.isObject()) {
                checkItem(what, expected.item, cast(what, DbObject.class, actual));
            } else if (key.endsWith(".txt")) {
                checkString(what, expected, actual);
            } else {
                checkBytes(what, expected.stored(), actual);
            }
        } else if (type == String.class) {
            checkString(what, expected, actual);
        } else if (type == DbObject.class) {
            checkItem(what, expected.item, cast(what, DbObject.class, actual));
        } else {
            Item item = cast(what, Item.class, actual);
            if (item.n != expected.item.n || !expected.item.s.equals(item.s)) {
                throw new AssertionError(what + ": expected " + expected + ", got Item("
                        + item.n + ", \"" + show(item.s) + "\")");
            }
        }
    }

    static void checkItem(String what, Item expected, DbObject actual) {
        if (actual.getInt("n") != expected.n || !expected.s.equals(actual.getString("s"))) {
            throw new AssertionError(what + ": expected Item(" + expected.n + ", \""
                    + show(expected.s) + "\"), got " + actual);
        }
    }

    static void checkBytes(String what, byte[] expected, Object actual) {
        if (!Arrays.equals(expected, cast(what, byte[].class, actual))) {
            throw new AssertionError(what + ": expected " + Arrays.toString(expected) + ", got "
                    + Arrays.toString((byte[]) actual));
        }
    }

    /** A value that is not an object as a String: decoded from UTF-8, as get() does. */
    static void checkString(String what, Val expected, Object actual) {
        if (expected.string == null && !isWellFormed(expected.bytes)) {
            throw new AssertionError(what + ": expected DataFormatException for bytes that are "
                    + "not well-formed UTF-8, " + expected + ", got " + actual);
        }
        String s = expected.string != null ? expected.string
                : new String(expected.bytes, StandardCharsets.UTF_8);
        if (!s.equals(cast(what, String.class, actual))) {
            throw new AssertionError(what + ": expected \"" + show(s) + "\", got \""
                    + show((String) actual) + "\"");
        }
    }

    static <T> T cast(String what, Class<T> c, Object actual) {
        if (!c.isInstance(actual)) {
            throw new AssertionError(what + ": expected a " + c.getSimpleName() + ", got a "
                    + actual.getClass().getSimpleName());
        }
        return c.cast(actual);
    }

    static String show(String s) {
        StringBuilder b = new StringBuilder();
        for (int i = 0; i < s.length(); i++) {
            char ch = s.charAt(i);
            if (ch < 0x20 || ch > 0x7e) {
                b.append(String.format("\\u%04x", (int) ch));
            } else {
                b.append(ch);
            }
        }
        return b.toString();
    }

    // ======== The run ========

    final long seed;
    final Random random;
    final TestClock clock = new TestClock();
    final StringBuilder trace = new StringBuilder();
    MemoryStream stream;
    Database db;
    Connection[] conns = new Connection[2];
    int step;
    /**
     * The bytes of a stored object: its first 1 to 3 bytes, or all but the last, are a
     * byte[] that starts as an object and is not one (bergdb 020-10, section 3.5).
     */
    byte[] objectBytes;
    long listings;
    long listed;

    PrimaryHarness(long seed) {
        this.seed = seed;
        this.random = new Random(seed);
    }

    /** Runs steps random steps on one seed; fails with the seed, the step and the last calls. */
    public static PrimaryHarness run(long seed, int steps) {
        PrimaryHarness h = new PrimaryHarness(seed);
        try {
            h.start(new MemoryStream());
            h.firstObject();
            for (h.step = 0; h.step < steps; h.step++) {
                h.step();
            }
        } catch (Throwable e) {
            AssertionError a = new AssertionError("PrimaryHarness, seed " + seed + ", step "
                    + h.step + ": " + e + "\nThe last calls:\n" + h.trace);
            a.initCause(e);
            throw a;
        } finally {
            if (h.db != null) {
                h.db.close();
            }
        }
        return h;
    }

    private void log(String s) {
        trace.append(step).append(": ").append(s).append('\n');
        if (trace.length() > 6000) {
            trace.delete(0, trace.indexOf("\n", trace.length() - 4000) + 1);
        }
    }

    private void start(MemoryStream m) {
        stream = m;
        db = ((DatabaseBuilderImp) Factory.database()).mainStream(m).clock(clock).start();
        conns[0] = db.connection();
        conns[1] = db.newConnection();
    }

    private void restart() {
        log("restart");
        db.close();
        db = null;
        start(stream.copy());
    }

    /** An object put outside the directories listed, for objectBytes. */
    private void firstObject() {
        String key = "/x/first";
        Val v = new Val(null, null, new Item(1, "first"));
        long t = conns[0].w().put(key, v.toPut()).execute().getTime().units();
        commit(t, Arrays.asList(key), Arrays.asList(v));
        objectBytes = conns[0].get(key, byte[].class).clone();
    }

    private void step() {
        if (random.nextInt(5) == 0) {
            clock.setTime(Time.units(clock.getTime() + random.nextInt(1000)));
        }
        Connection c = conns[random.nextInt(2)];
        int r = random.nextInt(100);
        if (r < 30) {
            w(c);
        } else if (r < 40) {
            rw(c);
        } else if (r < 44) {
            bulk(c);
        } else if (r < 46) {
            restart();
        } else {
            list(c);
        }
    }

    private String key() {
        String dir = DIRS[random.nextInt(4) == 0 ? random.nextInt(DIRS.length) : 0];
        if (dir.equals("/h/") && random.nextInt(4) == 0) {
            return dir + bulkName(random.nextInt(BULK));
        }
        return dir + NAMES[random.nextInt(NAMES.length)];
    }

    static String bulkName(int i) {
        return String.format("n%03d", i);
    }

    /** A value for key: an object at an object key now and then, else a String or byte[]. */
    private Val value(String key) {
        int r = random.nextInt(10);
        if (r < 4 && isObjectKey(key)) {
            int n = random.nextInt(8) == 0 ? (random.nextBoolean() ? Integer.MIN_VALUE
                    : Integer.MAX_VALUE) : random.nextInt();
            return new Val(null, null, new Item(n, text()));
        } else if (r < 7) {
            return new Val(text(), null, null);
        } else if (r < 8) {
            int n = random.nextBoolean() ? 1 + random.nextInt(3) : objectBytes.length - 1;
            return new Val(null, Arrays.copyOf(objectBytes, n), null);
        } else {
            byte[] b = new byte[random.nextInt(4) == 0 ? random.nextInt(2000) : random.nextInt(10)];
            random.nextBytes(b);
            if (b.length > 0 && (b[0] == 'b' || b[0] == (byte) 0x82)) {
                b[0] = 0;       // never the object header of format 1 or 2 (bergdb 020-07)
            }
            return new Val(null, b, null);
        }
    }

    /** Text without 'b', so that no String starts as an object of format 1 ("bergo"). */
    private String text() {
        int n = random.nextInt(8) == 0 ? random.nextInt(500) : random.nextInt(10);
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < n; i++) {
            int k = random.nextInt(12);
            if (k < 8) {
                sb.append("acdefghijk".charAt(random.nextInt(10)));
            } else if (k < 9) {
                sb.append('å');
            } else if (k < 10) {
                sb.append('€');
            } else if (k < 11) {
                sb.append("😀");
            } else {
                sb.append((char) random.nextInt(32));
            }
        }
        return sb.toString();
    }

    private void w(Connection c) {
        List<String> keys = new ArrayList<String>();
        List<Val> values = new ArrayList<Val>();
        WBuilder w = c.w();
        int n = 1 + random.nextInt(4);
        for (int i = 0; i < n; i++) {
            String key = key();
            Val v = random.nextInt(4) == 0 ? null : value(key);
            if (v == null) {
                w.delete(key);
            } else {
                w.put(key, v.toPut());
            }
            keys.add(key);
            values.add(v);
        }
        log("w " + keys + " " + values);
        commit(w.execute().getTime().units(), keys, values);
    }

    private void rw(Connection c) {
        final List<String> keys = new ArrayList<String>();
        final List<Val> values = new ArrayList<Val>();
        int n = 1 + random.nextInt(3);
        for (int i = 0; i < n; i++) {
            String key = key();
            keys.add(key);
            values.add(random.nextInt(4) == 0 ? null : value(key));
        }
        log("rw " + keys + " " + values);
        long t = c.rw(new Action() {
            public void run(RwEnvironment env) {
                for (int i = 0; i < keys.size(); i++) {
                    if (values.get(i) == null) {
                        env.delete(keys.get(i));
                    } else {
                        env.put(keys.get(i), values.get(i).toPut());
                    }
                }
            }
        }).getTime().units();
        commit(t, keys, values);
    }

    /**
     * A put in dir of a value of type's kind, if its name allows (an object needs an object
     * key), so that a listing at a later time would differ.
     */
    private void putIn(Connection c, String dir, Class<?> type) {
        String key = dir + NAMES[random.nextInt(NAMES.length)];
        Val v;
        if ((type == DbObject.class || type == Item.class) && isObjectKey(key)) {
            v = new Val(null, null, new Item(random.nextInt(), text()));
        } else {
            v = new Val(text(), null, null);
        }
        log("w [" + key + "] [" + v + "]");
        long t = c.w().put(key, v.toPut()).execute().getTime().units();
        commit(t, Arrays.asList(key), Arrays.asList(v));
    }

    /** Puts or deletes many names of /h/ in one w(): a listing then takes several pages. */
    private void bulk(Connection c) {
        List<String> keys = new ArrayList<String>();
        List<Val> values = new ArrayList<Val>();
        WBuilder w = c.w();
        boolean delete = random.nextInt(3) == 0;
        int from = random.nextInt(BULK);
        int to = from + 1 + random.nextInt(BULK - from);
        for (int i = from; i < to; i++) {
            String key = "/h/" + bulkName(i);
            Val v = delete ? null : value(key);
            if (v == null) {
                w.delete(key);
            } else {
                w.put(key, v.toPut());
            }
            keys.add(key);
            values.add(v);
        }
        log("bulk " + (delete ? "delete " : "put ") + from + " to " + to);
        commit(w.execute().getTime().units(), keys, values);
    }

    /** A listing, checked against the reference; now and then iterated twice. */
    private void list(Connection c) {
        int d = random.nextInt(10);
        String dir = d < 7 ? "/h/" : d < 8 ? "/h/sub/" : d < 9 ? "/" : "/h0/";
        Class<?> type = TYPES[random.nextInt(TYPES.length)];

        // The lookup time: the latest, a frozen one, one of the past, or before the first.
        long t;
        String timeString;
        int m = random.nextInt(10);
        if (m < 3) {
            c.setLookupTime(Time.MAX);
            t = Long.MAX_VALUE;
            timeString = "latest";
        } else if (m < 5) {
            c.freezeLookupTime();
            t = times.get(times.size() - 1);
            timeString = "frozen";
        } else if (m < 9) {
            t = Math.max(0, times.get(random.nextInt(times.size())) + random.nextInt(3) - 1);
            c.setLookupTime(Time.units(t));
            timeString = "at " + t;
        } else {
            t = times.get(0) - 1;
            c.setLookupTime(Time.units(t));
            timeString = "before the first, at " + t;
        }

        String startAt = null;
        boolean inclusive = true;
        boolean inclusiveCalled = random.nextBoolean();
        if (inclusiveCalled) {
            inclusive = random.nextBoolean();
        }
        if (random.nextBoolean()) {
            int s = random.nextInt(3);
            startAt = s == 0 ? NAMES[random.nextInt(NAMES.length)]
                    : s == 1 ? bulkName(random.nextInt(BULK))
                    : OTHER_STARTS[random.nextInt(OTHER_STARTS.length)];
        }
        boolean backward = random.nextBoolean();
        boolean kvs = random.nextBoolean();

        String what = "list " + dir + " as " + type.getSimpleName() + ", " + timeString
                + (startAt == null ? "" : ", startAt \"" + show(startAt) + "\"")
                + (inclusiveCalled ? ", inclusive " + inclusive : "")
                + (backward ? ", backward" : "") + (kvs ? ", kvs()" : ", objects()");
        log(what);

        UsePrimaryBuilder<?> b = c.usePrimary(type).dir(dir);
        // The calls after dir() in a random order.
        List<Integer> calls = new ArrayList<Integer>(Arrays.asList(0, 1, 2));
        java.util.Collections.shuffle(calls, random);
        for (int call : calls) {
            if (call == 0 && startAt != null) {
                b.startAt(startAt);
            } else if (call == 1 && inclusiveCalled) {
                b.inclusive(inclusive);
            } else if (call == 2 && backward) {
                b.backward();
            }
        }

        List<Map.Entry<String, Val>> expected = expected(dir, t, startAt, inclusive, backward,
                type);
        Iterable<?> iterable = kvs ? b.kvs() : b.objects();
        listings++;
        check(what, type, expected, iterable);

        if (random.nextInt(4) == 0 || timeString.equals("frozen")) {
            // A write in the directory, then the same Iterable again: at the same time. A
            // frozen time stays for a new listing and for a get.
            putIn(c, dir, type);
            log(what + ", again");
            check(what + ", again", type, expected, iterable);
            if (timeString.equals("frozen")) {
                UsePrimaryBuilder<?> again = c.usePrimary(type).dir(dir);
                if (startAt != null) {
                    again.startAt(startAt).inclusive(inclusive);
                }
                if (backward) {
                    again.backward();
                }
                check(what + ", a new listing at the frozen time", type, expected,
                        again.objects());
                if (!expected.isEmpty()) {
                    Map.Entry<String, Val> e = expected.get(random.nextInt(expected.size()));
                    if (!(type == Object.class && isTruncatedObject(e)) && !notUtf8(type, e)) {
                        Object got = c.get(e.getKey(), type);
                        checkValue("get(" + e.getKey() + ") at the frozen time", type,
                                e.getKey(), e.getValue(), got);
                    }
                }
            }
        }
    }

    private void check(String what, Class<?> type, List<Map.Entry<String, Val>> expected,
            Iterable<?> iterable) {
        Iterator<?> it = iterable.iterator();
        int i = 0;
        while (true) {
            boolean hasNext = it.hasNext();
            if (random.nextInt(8) == 0 && it.hasNext() != hasNext) {
                throw new AssertionError(what + ": hasNext() changed at " + i);
            }
            if (!hasNext) {
                break;
            }
            Object next;
            try {
                next = it.next();
            } catch (ObjectCreationException e) {
                if (type == Object.class && i < expected.size()
                        && isTruncatedObject(expected.get(i))) {
                    i++;
                    listed++;
                    continue;
                }
                throw e;
            } catch (DataFormatException e) {
                if (i < expected.size() && notUtf8(type, expected.get(i))) {
                    i++;
                    listed++;
                    continue;
                }
                throw e;
            }
            if (i >= expected.size()) {
                throw new AssertionError(what + ": more than the " + expected.size()
                        + " values expected: " + next);
            }
            Map.Entry<String, Val> e = expected.get(i);
            String at = what + ", value " + i + ", " + show(e.getKey());
            Object value = next;
            if (next instanceof Kv) {
                Kv<?> kv = (Kv<?>) next;
                if (!e.getKey().equals(kv.key())) {
                    throw new AssertionError(what + ", value " + i + ": expected the key "
                            + show(e.getKey()) + ", got " + show(kv.key()));
                }
                value = kv.value();
            }
            checkValue(at, type, e.getKey(), e.getValue(), value);
            i++;
            listed++;
        }
        if (i != expected.size()) {
            throw new AssertionError(what + ": " + i + " values, expected " + expected.size()
                    + (i < expected.size() ? ", the next " + show(expected.get(i).getKey()) : ""));
        }
        try {
            it.next();
            throw new AssertionError(what + ": next() after the end did not throw");
        } catch (NoSuchElementException e) {
            // Expected.
        }
    }

    /**
     * A byte[] at an object key of more than 3 bytes that starts as an object: get() as
     * Object gives it as a byte[] or throws ObjectCreationException, as the object format's
     * reader decides (format 1 throws, format 2 gives the byte[]; bergdb 020-08, section
     * 3), and the scan must give the same, which
     * PubTesterPrimary.testTruncatedObjectIsNotAnObject checks. Here either is taken.
     */
    boolean isTruncatedObject(Map.Entry<String, Val> e) {
        Val v = e.getValue();
        return v.bytes != null && v.bytes.length > 3 && isObjectKey(e.getKey())
                && Arrays.equals(v.bytes, Arrays.copyOf(objectBytes, v.bytes.length));
    }

    /**
     * True if the value e, of bytes that are not well-formed UTF-8, is read as a String by
     * type: get() and the scan throw DataFormatException (bergdb 021-06).
     */
    static boolean notUtf8(Class<?> type, Map.Entry<String, Val> e) {
        Val v = e.getValue();
        boolean asString = type == String.class 
                || (type == Object.class && e.getKey().endsWith(".txt"));
        return asString && v.bytes != null && !isWellFormed(v.bytes);
    }
    
    /** Well-formed UTF-8, by the JDK's decoder set to report. */
    static boolean isWellFormed(byte[] b) {
        try {
            StandardCharsets.UTF_8.newDecoder()
                    .onMalformedInput(java.nio.charset.CodingErrorAction.REPORT)
                    .onUnmappableCharacter(java.nio.charset.CodingErrorAction.REPORT)
                    .decode(java.nio.ByteBuffer.wrap(b));
            return true;
        } catch (java.nio.charset.CharacterCodingException e) {
            return false;
        }
    }
    
    // ======== Tests ========

    /** The unit test: 3 seeds of 500 steps (bergdb 020-10, section 9.4). */
    @Nano
    public static void testSeeds() {
        for (long seed = 1; seed <= 3; seed++) {
            run(seed, 500);
        }
    }

    /**
     * The night test: 30 seeds of 5,000 steps, new seeds each day (the day's number times
     * 1000), printed, so that a failure can be repeated with main(SEED, 5000).
     */
    @Nano("night")
    public static void testSeedsNight(TestEnvironment c) {
        long base = System.currentTimeMillis() / 86400000L * 1000;
        c.out().println("PrimaryHarness: seeds " + base + " to " + (base + 29)
                + ", 5000 steps each");
        for (long seed = base; seed < base + 30; seed++) {
            run(seed, 5000);
        }
    }

    /** Usage: PrimaryHarness [SEED [STEPS [RUNS]]]. */
    public static void main(String[] args) {
        long seed = args.length > 0 ? Long.parseLong(args[0]) : System.nanoTime();
        int steps = args.length > 1 ? Integer.parseInt(args[1]) : 5000;
        int runs = args.length > 2 ? Integer.parseInt(args[2]) : 1;
        for (int i = 0; i < runs; i++) {
            long t0 = System.nanoTime();
            PrimaryHarness h = run(seed + i, steps);
            System.out.println("PrimaryHarness: seed " + (seed + i) + ", " + steps + " steps, "
                    + h.listings + " listings, " + h.listed + " values listed, "
                    + (System.nanoTime() - t0) / 1000000 + " ms");
        }
        System.out.println("PrimaryHarness OK");
    }
}
