package bergdb.pubimp;

import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.SortedMap;
import java.util.TreeMap;
import java.util.TreeSet;

import bergdb.nanotest.Nano;

/**
 * The reference of the user indexes, for the tests: an index as a function of the data
 * (bergdb 020-10, section 3.3) and the result of a scan (section 3.4), computed from Java
 * values, apart from the code: no encoded bytes, no class of the indexes. With a model of
 * the data, each key's versions by time, and of the indexes, each generation's creation,
 * activation and deletion. Harness H2 (IndexHarness, bergdb 020-10, section 9.1) runs
 * BergDB against it; other tests may use its f.
 *
 * <p>Values are Java values. An object is a Map from field names to values; a field's value
 * is a Long (every integer: one integer type, bergdb 020-02, section 4.7), a Double, a
 * String, a Bin (a byte[]), a Boolean, a List (an array) or a Map (an object). A key's value
 * is an object, a String, a Bin, or null (no value). A Bin is never an object: bytes that
 * start with 0x82 are taken as bytes that fail format 2's full check (bergdb 020-08,
 * section 3), and a Bin that is a whole object of format 1 (ObjectFormat.isFormat1) is
 * refused (020-08, step 3 and section 3), so IndexHarness's generator makes neither of the
 * others: no Bin of it starts with 0x82 or "bergo".</p>
 *
 * <p>A reference may hold a planted fault (Fault), so that a harness can show that it
 * finds such a fault (bergdb 020-10, section 9.1, "its own check").</p>
 */
final class IndexReference {

    /** A level's type (bergdb 020-10, section 3.1), by its type string. */
    enum Type {
        LONG("long"), DOUBLE("double"), STRING("string"), BYTES("bytes");

        final String string;

        Type(String string) {
            this.string = string;
        }
    }

    /**
     * The faults that a reference can plant, one at a time (bergdb 020-10, section 9.1): an
     * entry not deleted (a value's earlier entries kept in the index), a bound off by one (an
     * exclusive lower bound taken as inclusive), and -0.0 apart from 0.0.
     */
    enum Fault {
        NONE, ENTRY_NOT_DELETED, BOUND_OFF_BY_ONE, NEG_ZERO_APART
    }

    /** The most bytes of levels an entry has (bergdb 020-10, section 3.3). */
    static final int MAX_LEVEL_BYTES = 4096;

    /** How a harness gives a level's path to IndexBuilder; the reference reads the path only. */
    enum Call {
        /** field(name): one part, a '.' in it is part of the name. */
        FIELD,
        /** nestedField("a.b"): the parts split at '.'. */
        NESTED_STRING,
        /** nestedField(new String[] {...}). */
        NESTED_ARRAY
    }

    /** A byte[] as a value: equal by content, ordered by unsigned bytes. */
    static final class Bin implements Comparable<Bin> {
        private final byte[] b;

        Bin(byte[] b) {
            this.b = b.clone();
        }

        static Bin of(int... bytes) {
            byte[] b = new byte[bytes.length];
            for (int i = 0; i < b.length; i++) {
                b[i] = (byte) bytes[i];
            }
            return new Bin(b);
        }

        byte[] bytes() {
            return b.clone();
        }

        int length() {
            return b.length;
        }

        boolean startsWith(Bin p) {
            return p.b.length <= b.length && Arrays.equals(b, 0, p.b.length, p.b, 0, p.b.length);
        }

        Bin prefix(int length) {
            return new Bin(Arrays.copyOf(b, length));
        }

        public int compareTo(Bin o) {
            return Arrays.compareUnsigned(b, o.b);
        }

        public boolean equals(Object o) {
            return o instanceof Bin && Arrays.equals(b, ((Bin) o).b);
        }

        public int hashCode() {
            return Arrays.hashCode(b);
        }

        public String toString() {
            StringBuilder s = new StringBuilder("0x");
            for (byte x : b) {
                s.append(String.format("%02x", x & 0xff));
            }
            return s.toString();
        }
    }

    /** A level of an index: its type and its field's path (1 to 16 names). */
    static final class Level {
        final Type type;
        final String[] path;
        final Call call;

        Level(Type type, Call call, String... path) {
            this.type = type;
            this.call = call;
            this.path = path.clone();
        }

        public String toString() {
            return type.string + " " + String.join("|", path);
        }
    }

    /** An index's definition: its name, its directory and its levels (1 to 8). */
    static final class Def {
        final String name;
        final String dir;
        final List<Level> levels;

        Def(String name, String dir, List<Level> levels) {
            this.name = name;
            this.dir = dir;
            this.levels = Collections.unmodifiableList(new ArrayList<Level>(levels));
        }

        Type type(int level) {
            return levels.get(level).type;
        }

        public String toString() {
            return show(name) + " on " + dir + " " + levels;
        }
    }

    /**
     * An entry of an index: its levels' values (Long, Double, String, Bin) and its key; and,
     * for a scan, the key's value. Equal by levels and key.
     */
    static final class Entry {
        final List<Object> levels;
        final String key;
        final Object value;

        Entry(List<Object> levels, String key, Object value) {
            this.levels = Collections.unmodifiableList(new ArrayList<Object>(levels));
            this.key = key;
            this.value = value;
        }

        public boolean equals(Object o) {
            return o instanceof Entry && ((Entry) o).levels.equals(levels)
                    && ((Entry) o).key.equals(key);
        }

        public int hashCode() {
            return levels.hashCode() * 31 + key.hashCode();
        }

        public String toString() {
            return show(levels) + " " + show(key);
        }
    }

    /**
     * A scan (bergdb 020-10, section 3.4): eq on levels 1 to k, then on level k + 1 a lower
     * bound, an upper bound, both, or a prefix, or nothing; and the direction. The values
     * are Long, Double, String or Bin, as the levels' types; null for none.
     */
    static final class Query {
        final List<Object> eq;
        final Object from;
        final boolean fromInclusive;
        final Object to;
        final boolean toInclusive;
        final Object prefix;
        final boolean backward;

        Query(List<Object> eq, Object from, boolean fromInclusive, Object to,
                boolean toInclusive, Object prefix, boolean backward) {
            this.eq = Collections.unmodifiableList(new ArrayList<Object>(eq));
            this.from = from;
            this.fromInclusive = fromInclusive;
            this.to = to;
            this.toInclusive = toInclusive;
            this.prefix = prefix;
            this.backward = backward;
        }

        /** The level that from, to or prefix is on, 0-based: eq's size. */
        int rangeLevel() {
            return eq.size();
        }

        boolean hasRange() {
            return from != null || to != null || prefix != null;
        }

        /**
         * Checks the query against the grammar of bergdb 020-10, section 3.4, for def:
         * IllegalArgumentException if it does not hold. eq on at most n levels, a bound or a
         * prefix only on a level after them (so eq on fewer than n levels), not a prefix and a
         * bound together, each value of its level's type, a prefix only on a string or bytes
         * level, no NaN.
         */
        void check(Def def) {
            int n = def.levels.size();
            if (eq.size() > n || hasRange() && eq.size() >= n) {
                throw new IllegalArgumentException("levels: " + this + " on " + def);
            }
            if (prefix != null && (from != null || to != null)) {
                throw new IllegalArgumentException("a prefix and a bound: " + this);
            }
            for (int i = 0; i < eq.size(); i++) {
                checkValue(def.type(i), eq.get(i));
            }
            if (hasRange()) {
                Type t = def.type(eq.size());
                if (from != null) {
                    checkValue(t, from);
                }
                if (to != null) {
                    checkValue(t, to);
                }
                if (prefix != null && !(t == Type.STRING && prefix instanceof String
                        || t == Type.BYTES && prefix instanceof Bin)) {
                    throw new IllegalArgumentException("prefix " + show(prefix) + " on " + t);
                }
            }
        }

        private static void checkValue(Type t, Object v) {
            if (v == null || v.getClass() != javaClass(t)
                    || v instanceof Double && Double.isNaN((Double) v)) {
                throw new IllegalArgumentException(show(v) + " for a level of type " + t);
            }
        }

        public String toString() {
            StringBuilder s = new StringBuilder();
            for (Object v : eq) {
                s.append(".eq(").append(show(v)).append(")");
            }
            if (from != null) {
                s.append(".from(").append(show(from)).append(", ").append(fromInclusive).append(")");
            }
            if (to != null) {
                s.append(".to(").append(show(to)).append(", ").append(toInclusive).append(")");
            }
            if (prefix != null) {
                s.append(".prefix(").append(show(prefix)).append(")");
            }
            if (backward) {
                s.append(".backward()");
            }
            return s.length() == 0 ? "(all)" : s.toString();
        }
    }

    /** The Java class of a level's values. */
    static Class<?> javaClass(Type t) {
        switch (t) {
        case LONG:
            return Long.class;
        case DOUBLE:
            return Double.class;
        case STRING:
            return String.class;
        default:
            return Bin.class;
        }
    }

    // ======== The function and the order ========

    final Fault fault;

    IndexReference() {
        this(Fault.NONE);
    }

    IndexReference(Fault fault) {
        this.fault = fault;
    }

    /**
     * f (bergdb 020-10, section 3.3): the levels of the one entry of value at key, or null
     * for no entry. No entry for a key with a suffix (not .obj), a value that is not an
     * object, a level whose path is absent or goes through a field that is not an object, a
     * value of another kind than the level's type (no kind converted), NaN, or levels of more
     * than 4,096 bytes in all. -0.0 is 0.0.
     */
    List<Object> f(Def def, String key, Object value) {
        if (!isObjectKey(key) || !(value instanceof Map)) {
            return null;
        }
        List<Object> levels = new ArrayList<Object>();
        int size = 0;
        for (Level level : def.levels) {
            Object v = levelValue(level.type, follow((Map<?, ?>) value, level.path));
            if (v == null) {
                return null;
            }
            size += encodedSize(level.type, v);
            levels.add(v);
        }
        return size > MAX_LEVEL_BYTES ? null : levels;
    }

    /** The value at path in the object o, or null if a part is absent or not an object. */
    static Object follow(Map<?, ?> o, String[] path) {
        Object v = o;
        for (String part : path) {
            if (!(v instanceof Map)) {
                return null;
            }
            v = ((Map<?, ?>) v).get(part);
        }
        return v;
    }

    /** v as a level of type t, or null if it is not of t's kind or is NaN; -0.0 is 0.0. */
    Object levelValue(Type t, Object v) {
        if (v == null || v.getClass() != javaClass(t)) {
            return null;
        }
        if (v instanceof Double) {
            double d = (Double) v;
            if (Double.isNaN(d)) {
                return null;
            }
            return normalized(d);
        }
        return v;
    }

    /** -0.0 as 0.0, unless the fault NEG_ZERO_APART is planted. */
    private Double normalized(double d) {
        return d == 0.0 && fault != Fault.NEG_ZERO_APART ? 0.0 : d;
    }

    /** A query's argument as a level value: -0.0 is 0.0 (bergdb 020-10, section 3.4). */
    private Object argument(Object v) {
        return v instanceof Double ? normalized((Double) v) : v;
    }

    /**
     * Whether key is an object key: no suffix, or .obj, as Entries.isObjectKey (the suffix is
     * what follows the last '.' of the key's last part, a name that starts with '.' too; a '.'
     * in a directory's name is not one, bergdb 021-10).
     */
    static boolean isObjectKey(String key) {
        int i = key.lastIndexOf('.');
        String suffix = i <= key.lastIndexOf('/') ? "" : key.substring(i + 1);
        return suffix.isEmpty() || suffix.equals("obj");
    }

    /**
     * The bytes a level takes in an entry (bergdb 020-10, section 4.4): 8 for a long and a
     * double; for a string (its UTF-8) and bytes, each byte, each 00 and 01 twice, and a
     * final 00.
     */
    static int encodedSize(Type t, Object v) {
        byte[] b;
        if (t == Type.LONG || t == Type.DOUBLE) {
            return 8;
        } else if (t == Type.STRING) {
            b = ((String) v).getBytes(StandardCharsets.UTF_8);
        } else {
            b = ((Bin) v).b;
        }
        int size = b.length + 1;
        for (byte x : b) {
            if (x == 0 || x == 1) {
                size++;
            }
        }
        return size;
    }

    /**
     * The order of a level's values: Long.compare, Double.compare (with -0.0 made 0.0 before),
     * strings by code points, bytes by unsigned bytes.
     */
    static int compareLevel(Type t, Object a, Object b) {
        switch (t) {
        case LONG:
            return Long.compare((Long) a, (Long) b);
        case DOUBLE:
            return Double.compare((Double) a, (Double) b);
        case STRING:
            return compareCodePoints((String) a, (String) b);
        default:
            return ((Bin) a).compareTo((Bin) b);
        }
    }

    /** Strings by code points (and so by their UTF-8), not by Java's UTF-16 chars. */
    static int compareCodePoints(String a, String b) {
        int i = 0;
        int j = 0;
        while (i < a.length() && j < b.length()) {
            int ca = a.codePointAt(i);
            int cb = b.codePointAt(j);
            if (ca != cb) {
                return Integer.compare(ca, cb);
            }
            i += Character.charCount(ca);
            j += Character.charCount(cb);
        }
        return (i < a.length() ? 1 : 0) - (j < b.length() ? 1 : 0);
    }

    /** The index's order: the levels as a tuple, then the key (bergdb 020-10, section 3.4). */
    static Comparator<Entry> order(final Def def) {
        return new Comparator<Entry>() {
            public int compare(Entry a, Entry b) {
                for (int i = 0; i < def.levels.size(); i++) {
                    int c = compareLevel(def.type(i), a.levels.get(i), b.levels.get(i));
                    if (c != 0) {
                        return c;
                    }
                }
                return compareCodePoints(a.key, b.key);
            }
        };
    }

    // ======== Entries and scans ========

    /**
     * The entries of the index over values, the values of its directory's own keys at a
     * lookup time (a key to its value), in the index's order.
     */
    List<Entry> entries(Def def, Map<String, Object> values) {
        List<Entry> result = new ArrayList<Entry>();
        for (Map.Entry<String, Object> e : values.entrySet()) {
            List<Object> levels = f(def, e.getKey(), e.getValue());
            if (levels != null) {
                result.add(new Entry(levels, e.getKey(), e.getValue()));
            }
        }
        Collections.sort(result, order(def));
        return result;
    }

    /**
     * The result of the scan q of the index over values (bergdb 020-10, section 3.4): the
     * entries whose levels 1 to k equal eq's values and whose level k + 1 meets the bounds
     * or the prefix, in the index's order or backward; each with its key's value.
     */
    List<Entry> scan(Def def, Map<String, Object> values, Query q) {
        return filter(def, entries(def, values), q);
    }

    /** The scan q over entries, the index's entries in its order (from entries()). */
    List<Entry> filter(Def def, List<Entry> entries, Query q) {
        q.check(def);
        List<Entry> result = new ArrayList<Entry>();
        for (Entry e : entries) {
            if (matches(def, q, e.levels)) {
                result.add(e);
            }
        }
        if (q.backward) {
            Collections.reverse(result);
        }
        return result;
    }

    /** Whether an entry's levels meet the query. */
    boolean matches(Def def, Query q, List<Object> levels) {
        int k = q.eq.size();
        for (int i = 0; i < k; i++) {
            if (compareLevel(def.type(i), levels.get(i), argument(q.eq.get(i))) != 0) {
                return false;
            }
        }
        if (!q.hasRange()) {
            return true;
        }
        Type t = def.type(k);
        Object v = levels.get(k);
        if (q.from != null) {
            int c = compareLevel(t, v, argument(q.from));
            boolean inclusive = q.fromInclusive || fault == Fault.BOUND_OFF_BY_ONE;
            if (c < 0 || c == 0 && !inclusive) {
                return false;
            }
        }
        if (q.to != null) {
            int c = compareLevel(t, v, argument(q.to));
            if (c > 0 || c == 0 && !q.toInclusive) {
                return false;
            }
        }
        if (q.prefix instanceof String) {
            // Well-formed strings: a prefix by chars is a prefix by code points and by UTF-8.
            return ((String) v).startsWith((String) q.prefix);
        } else if (q.prefix instanceof Bin) {
            return ((Bin) v).startsWith((Bin) q.prefix);
        }
        return true;
    }

    /**
     * The entries that the generation g's index must hold at the lookup time t in the model
     * m, by f over the values of its directory's own keys at t, in the index's order: for an
     * active index exactly these, for a building one some of them. With the fault
     * ENTRY_NOT_DELETED, also the entries of the values each key had since the index's
     * creation.
     */
    List<Entry> expectedEntries(Model m, Generation g, long t) {
        if (fault != Fault.ENTRY_NOT_DELETED) {
            return entries(g.def, m.dirAt(g.def.dir, t));
        }
        TreeSet<Entry> set = new TreeSet<Entry>(order(g.def));
        for (Map.Entry<String, TreeMap<Long, Object>> e : m.versions.entrySet()) {
            if (!Model.inDir(e.getKey(), g.def.dir)) {
                continue;
            }
            // Each version that was the key's value at a time from the creation to t.
            for (Map.Entry<Long, Object> v : e.getValue().headMap(t, true).entrySet()) {
                Long next = e.getValue().higherKey(v.getKey());
                if (next != null && next <= g.created.hi) {
                    continue;
                }
                List<Object> levels = f(g.def, e.getKey(), v.getValue());
                if (levels != null) {
                    set.add(new Entry(levels, e.getKey(), v.getValue()));
                }
            }
        }
        return new ArrayList<Entry>(set);
    }

    // ======== The model ========

    /** A put (value not null) or a delete (value null) of a transaction. */
    static final class Write {
        final String key;
        final Object value;

        Write(String key, Object value) {
            this.key = key;
            this.value = value;
        }

        public String toString() {
            return value == null ? "delete " + show(key) : "put " + show(key) + " " + show(value);
        }
    }

    /**
     * The time of a change that the harness does not see exactly, such as a background
     * build's activation: lo < T <= hi. hi is Long.MAX_VALUE until known; lo and hi both
     * Long.MAX_VALUE for a change that has not happened (a deletion not made).
     */
    static final class Interval {
        long lo;
        long hi;

        Interval(long lo, long hi) {
            set(lo, hi);
        }

        void set(long lo, long hi) {
            if (lo >= hi && lo != Long.MAX_VALUE) {
                throw new IllegalArgumentException("interval (" + lo + ", " + hi + "]");
            }
            this.lo = lo;
            this.hi = hi;
        }

        /** -1 if t is before the change, 1 if at or after it, 0 if unknown. */
        int at(long t) {
            return t <= lo ? -1 : t >= hi ? 1 : 0;
        }

        /** Seen done at t: T <= t. Throws if it was seen not done at t or later. */
        void doneAt(long t) {
            if (t <= lo) {
                throw new AssertionError("done at " + t + ", but not done at " + lo);
            }
            hi = Math.min(hi, t);
        }

        /** Seen not done at t: T > t. Throws if it was seen done at t or earlier. */
        void notDoneAt(long t) {
            if (t >= hi) {
                throw new AssertionError("not done at " + t + ", but done at " + hi);
            }
            lo = Math.max(lo, t);
        }

        public String toString() {
            return "(" + (lo == Long.MAX_VALUE ? "never" : lo) + ", "
                    + (hi == Long.MAX_VALUE ? "?" : hi) + "]";
        }
    }

    /** The state of an index at a lookup time, as useIndex sees it. */
    enum State {
        ABSENT, BUILDING, ACTIVE, UNKNOWN
    }

    /**
     * An index's generation (bergdb 020-10, section 4.3): one creation of a name, from its
     * creation to its deletion, with its activation between when its build ends.
     */
    static final class Generation {
        final Def def;
        final Interval created;
        final Interval activated;
        final Interval deleted = new Interval(Long.MAX_VALUE, Long.MAX_VALUE);
        /** Its G, if the harness learns it; else -1. */
        long g = -1;

        Generation(Def def, long createdLo, long createdHi) {
            this.def = def;
            this.created = new Interval(createdLo, createdHi);
            this.activated = new Interval(createdLo, Long.MAX_VALUE);
        }

        boolean isDeleted() {
            return deleted.lo != Long.MAX_VALUE;
        }

        State stateAt(long t) {
            int c = created.at(t);
            int d = deleted.at(t);
            if (c < 0 || d > 0) {
                return State.ABSENT;
            }
            if (c == 0 || d == 0) {
                return State.UNKNOWN;
            }
            int a = activated.at(t);
            return a < 0 ? State.BUILDING : a > 0 ? State.ACTIVE : State.UNKNOWN;
        }

        public String toString() {
            return def + ", created " + created + ", activated " + activated + ", deleted "
                    + deleted;
        }
    }

    /**
     * The model of a database's data and indexes: each key's versions by time (a value, or
     * null for none), and each index's generations. Transactions may be committed in any
     * order of their times (writer threads), each time once.
     */
    static final class Model {
        final TreeMap<String, TreeMap<Long, Object>> versions =
                new TreeMap<String, TreeMap<Long, Object>>();
        final TreeSet<Long> times = new TreeSet<Long>();
        final List<Generation> generations = new ArrayList<Generation>();

        /** A transaction's writes at its time; for a key written twice, the last wins. */
        void commit(long time, List<Write> writes) {
            if (!times.add(time)) {
                throw new AssertionError("two transactions at the time " + time);
            }
            LinkedHashMap<String, Object> last = new LinkedHashMap<String, Object>();
            for (Write w : writes) {
                last.remove(w.key);
                last.put(w.key, w.value);
            }
            for (Map.Entry<String, Object> e : last.entrySet()) {
                TreeMap<Long, Object> v = versions.get(e.getKey());
                if (v == null) {
                    v = new TreeMap<Long, Object>();
                    versions.put(e.getKey(), v);
                }
                v.put(time, e.getValue());
            }
        }

        /** The time of the latest transaction committed, or -1. */
        long lastTime() {
            return times.isEmpty() ? -1 : times.last();
        }

        /** The key's value at the lookup time t, or null. */
        Object valueAt(String key, long t) {
            TreeMap<Long, Object> v = versions.get(key);
            Map.Entry<Long, Object> e = v == null ? null : v.floorEntry(t);
            return e == null ? null : e.getValue();
        }

        /** The values of dir's own keys (not its subdirectories') at t, by key. */
        SortedMap<String, Object> dirAt(String dir, long t) {
            TreeMap<String, Object> result = new TreeMap<String, Object>();
            for (String key : versions.keySet()) {
                if (inDir(key, dir)) {
                    Object v = valueAt(key, t);
                    if (v != null) {
                        result.put(key, v);
                    }
                }
            }
            return result;
        }

        /** Whether key is one of dir's own keys. */
        static boolean inDir(String key, String dir) {
            return key.startsWith(dir) && key.indexOf('/', dir.length()) < 0;
        }

        /** A new generation of def, created in (lo, hi]. */
        Generation create(Def def, long lo, long hi) {
            if (live(def.name) != null) {
                throw new AssertionError("a creation of a used name: " + def);
            }
            Generation g = new Generation(def, lo, hi);
            generations.add(g);
            return g;
        }

        /** The generation of the name that is not deleted, or null. */
        Generation live(String name) {
            for (Generation g : generations) {
                if (g.def.name.equals(name) && !g.isDeleted()) {
                    return g;
                }
            }
            return null;
        }

        /** The generations of the name whose state at t is not ABSENT (at most one known). */
        List<Generation> at(String name, long t) {
            List<Generation> result = new ArrayList<Generation>();
            for (Generation g : generations) {
                if (g.def.name.equals(name) && g.stateAt(t) != State.ABSENT) {
                    result.add(g);
                }
            }
            return result;
        }
    }

    // ======== Showing values ========

    /** A value as text, for a failure's message: strings quoted, other chars escaped. */
    static String show(Object v) {
        if (v instanceof String) {
            StringBuilder s = new StringBuilder("\"");
            String str = (String) v;
            if (str.length() > 40) {
                return "\"" + escape(str.substring(0, 20)) + "...\" (" + str.length() + " chars)";
            }
            return s.append(escape(str)).append('"').toString();
        } else if (v instanceof Map) {
            StringBuilder s = new StringBuilder("{");
            for (Map.Entry<?, ?> e : ((Map<?, ?>) v).entrySet()) {
                s.append(s.length() > 1 ? ", " : "").append(show(e.getKey())).append(": ")
                        .append(show(e.getValue()));
            }
            return s.append('}').toString();
        } else if (v instanceof List) {
            StringBuilder s = new StringBuilder("[");
            for (Object x : (List<?>) v) {
                s.append(s.length() > 1 ? ", " : "").append(show(x));
            }
            return s.append(']').toString();
        } else if (v instanceof Double && (Double) v == 0.0) {
            return 1 / (Double) v < 0 ? "-0.0" : "0.0";
        } else if (v instanceof Bin && ((Bin) v).length() > 40) {
            return ((Bin) v).prefix(20) + "... (" + ((Bin) v).length() + " bytes)";
        }
        return String.valueOf(v);
    }

    private static String escape(String s) {
        StringBuilder b = new StringBuilder();
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            if (c >= 0x20 && c < 0x7f && c != '"' && c != '\\') {
                b.append(c);
            } else {
                b.append(String.format("\\u%04x", (int) c));
            }
        }
        return b.toString();
    }

    // ======== Tests of the reference ========

    static Level level(Type t, String... path) {
        return new Level(t, path.length == 1 ? Call.FIELD : Call.NESTED_ARRAY, path);
    }

    static Def def(String dir, Level... levels) {
        return new Def("i", dir, Arrays.asList(levels));
    }

    static TreeMap<String, Object> obj(Object... namesAndValues) {
        TreeMap<String, Object> o = new TreeMap<String, Object>();
        for (int i = 0; i < namesAndValues.length; i += 2) {
            o.put((String) namesAndValues[i], namesAndValues[i + 1]);
        }
        return o;
    }

    static List<Object> list(Object... values) {
        return Arrays.asList(values);
    }

    private static void check(boolean ok, String message) {
        if (!ok) {
            throw new AssertionError(message);
        }
    }

    private static void checkF(IndexReference ref, Def d, String key, Object value,
            List<Object> expected) {
        List<Object> got = ref.f(d, key, value);
        check(expected == null ? got == null : expected.equals(got), "f(" + show(key) + ", "
                + show(value) + ") on " + d + ": " + show(got) + ", not " + show(expected));
    }

    /** f by 020-10, section 3.3's table: each type takes its stored kind, and no other. */
    @Nano
    public static void testFunctionByKind() {
        IndexReference ref = new IndexReference();
        Object[] values = {5L, 2.5, "s", Bin.of(1, 2), true, list(1L), obj("a", 1L)};
        for (Type t : Type.values()) {
            Def d = def("/h/", level(t, "a"));
            for (Object v : values) {
                boolean taken = v.getClass() == javaClass(t);
                checkF(ref, d, "/h/k", obj("a", v), taken ? list(v) : null);
            }
            checkF(ref, d, "/h/k", obj("b", values[t.ordinal()]), null);
            checkF(ref, d, "/h/k", obj(), null);
        }
        Def dd = def("/h/", level(Type.DOUBLE, "a"));
        checkF(ref, dd, "/h/k", obj("a", Double.NaN), null);
        checkF(ref, dd, "/h/k", obj("a", Double.longBitsToDouble(0x7ff0000000000001L)), null);
        checkF(ref, dd, "/h/k", obj("a", -0.0), list(0.0));
        check(1 / (Double) ref.f(dd, "/h/k", obj("a", -0.0)).get(0) > 0, "-0.0 is 0.0");
        checkF(ref, dd, "/h/k", obj("a", Double.NEGATIVE_INFINITY),
                list(Double.NEGATIVE_INFINITY));
    }

    /** No entry for a key with a suffix, or a value that is not an object; .obj is an object key. */
    @Nano
    public static void testFunctionKeysAndValues() {
        IndexReference ref = new IndexReference();
        Def d = def("/h/", level(Type.STRING, "a"));
        Map<String, Object> o = obj("a", "x");
        checkF(ref, d, "/h/k", o, list("x"));
        checkF(ref, d, "/h/k.obj", o, list("x"));
        checkF(ref, d, "/h/k.txt", o, null);
        checkF(ref, d, "/h/k.bin", o, null);
        checkF(ref, d, "/h/k", "a string", null);
        checkF(ref, d, "/h/k", Bin.of(0x82, 0xff), null);
        checkF(ref, d, "/h/k", null, null);
        check(isObjectKey("/h/k") && isObjectKey("/h/k.obj") && !isObjectKey("/h/.k")
                && !isObjectKey("/h/k.txt") && isObjectKey("/h.1/k"), "isObjectKey");
    }

    /** Paths: nested objects, a '.' in a name, absent parts and parts that are not objects. */
    @Nano
    public static void testFunctionPaths() {
        IndexReference ref = new IndexReference();
        Def nested = def("/h/", level(Type.LONG, "n", "m", "a"));
        checkF(ref, nested, "/h/k", obj("n", obj("m", obj("a", 7L))), list(7L));
        checkF(ref, nested, "/h/k", obj("n", obj("m", 5L)), null);
        checkF(ref, nested, "/h/k", obj("n", obj("x", obj("a", 7L))), null);
        checkF(ref, nested, "/h/k", obj("n", list(obj("m", obj("a", 7L)))), null);
        checkF(ref, nested, "/h/k", obj("n", "m"), null);
        Def dotted = def("/h/", level(Type.LONG, "x.y"));
        checkF(ref, dotted, "/h/k", obj("x.y", 3L), list(3L));
        checkF(ref, dotted, "/h/k", obj("x", obj("y", 3L)), null);
        Def object = def("/h/", level(Type.LONG, "n"));
        checkF(ref, object, "/h/k", obj("n", obj("a", 1L)), null);
        Def two = def("/h/", level(Type.STRING, "a"), level(Type.DOUBLE, "n", "b"));
        checkF(ref, two, "/h/k", obj("a", "s", "n", obj("b", 1.5)), list("s", 1.5));
        checkF(ref, two, "/h/k", obj("a", "s", "n", obj("b", 1L)), null);
        checkF(ref, two, "/h/k", obj("a", "s"), null);
    }

    /** The 4,096 bytes of levels: an entry at 4,096, none at 4,097; 00 and 01 count twice. */
    @Nano
    public static void testFunctionSizeLimit() {
        IndexReference ref = new IndexReference();
        Def s = def("/h/", level(Type.STRING, "a"));
        checkF(ref, s, "/h/k", obj("a", repeat("a", 4095)), list(repeat("a", 4095)));
        checkF(ref, s, "/h/k", obj("a", repeat("a", 4096)), null);
        checkF(ref, s, "/h/k", obj("a", repeat("\u0000", 2047)), list(repeat("\u0000", 2047)));
        checkF(ref, s, "/h/k", obj("a", repeat("\u0001", 2048)), null);
        // U+00E9 is two bytes of UTF-8.
        checkF(ref, s, "/h/k", obj("a", repeat("é", 2047) + "a"),
                list(repeat("é", 2047) + "a"));
        checkF(ref, s, "/h/k", obj("a", repeat("é", 2048)), null);
        Def sl = def("/h/", level(Type.STRING, "a"), level(Type.LONG, "b"));
        checkF(ref, sl, "/h/k", obj("a", repeat("a", 4087), "b", 1L), list(repeat("a", 4087), 1L));
        checkF(ref, sl, "/h/k", obj("a", repeat("a", 4088), "b", 1L), null);
        Def b = def("/h/", level(Type.BYTES, "a"));
        byte[] zeros = new byte[2047];
        checkF(ref, b, "/h/k", obj("a", new Bin(zeros)), list(new Bin(zeros)));
        checkF(ref, b, "/h/k", obj("a", new Bin(new byte[2048])), null);
        check(encodedSize(Type.BYTES, Bin.of()) == 1 && encodedSize(Type.STRING, "") == 1
                && encodedSize(Type.BYTES, Bin.of(0, 1, 2)) == 6, "encodedSize");
    }

    static String repeat(String s, int n) {
        StringBuilder b = new StringBuilder();
        for (int i = 0; i < n; i++) {
            b.append(s);
        }
        return b.toString();
    }

    /** Strings by code points, not by UTF-16: U+FFFF before U+1F600. */
    @Nano
    public static void testCodePointOrder() {
        String[] ordered = {"", "\u0000", "\u0001", "a", "a\u0000", "a\u0001", "ab", "é",
                "￿", "𐀀", "😀", "😀a"};
        for (int i = 0; i < ordered.length; i++) {
            for (int j = 0; j < ordered.length; j++) {
                int c = compareCodePoints(ordered[i], ordered[j]);
                check(Integer.signum(c) == Integer.signum(Integer.compare(i, j)),
                        show(ordered[i]) + " against " + show(ordered[j]) + ": " + c);
            }
        }
        check("￿".compareTo("😀") > 0, "UTF-16's order differs");
    }

    /** Scans: eq, bounds each inclusive or not, a prefix, backward, from above to, -0.0. */
    @Nano
    public static void testScan() {
        IndexReference ref = new IndexReference();
        Def d = def("/h/", level(Type.STRING, "a"), level(Type.DOUBLE, "b"));
        TreeMap<String, Object> values = new TreeMap<String, Object>();
        values.put("/h/k1", obj("a", "x", "b", 1.0));
        values.put("/h/k2", obj("a", "x", "b", -0.0));
        values.put("/h/k3", obj("a", "x", "b", 0.0));
        values.put("/h/k4", obj("a", "x😀", "b", 2.0));
        values.put("/h/k5", obj("a", "x￿", "b", 2.0));
        values.put("/h/k6", obj("a", "y", "b", Double.NaN));
        values.put("/h/k7", "x");
        values.put("/h/k8", obj("a", "", "b", Double.NEGATIVE_INFINITY));
        checkScan(ref, d, values, all(), "k8 k2 k3 k1 k5 k4");
        checkScan(ref, d, values, q(list("x"), null, false, null, false, null, false), "k2 k3 k1");
        checkScan(ref, d, values, q(list("x", -0.0), null, false, null, false, null, false),
                "k2 k3");
        checkScan(ref, d, values, q(list("x"), 0.0, false, null, false, null, false), "k1");
        checkScan(ref, d, values, q(list("x"), -0.0, true, 1.0, false, null, false), "k2 k3");
        checkScan(ref, d, values, q(list("x"), 0.0, true, 1.0, true, null, true), "k1 k3 k2");
        checkScan(ref, d, values, q(list("x"), 1.0, true, 0.0, true, null, false), "");
        checkScan(ref, d, values, q(list(), null, false, null, false, "x", false), "k2 k3 k1 k5 k4");
        checkScan(ref, d, values, q(list(), null, false, null, false, "x￿", true), "k5");
        checkScan(ref, d, values, q(list(), null, false, null, false, "", false),
                "k8 k2 k3 k1 k5 k4");
        checkScan(ref, d, values, q(list(), "x￿", false, null, false, null, false), "k4");
        Def bytes = def("/h/", level(Type.BYTES, "a"));
        TreeMap<String, Object> bv = new TreeMap<String, Object>();
        bv.put("/h/k1", obj("a", Bin.of(0, 1)));
        bv.put("/h/k2", obj("a", Bin.of(0)));
        bv.put("/h/k3", obj("a", Bin.of(0xff)));
        bv.put("/h/k4", obj("a", Bin.of()));
        bv.put("/h/k5", obj("a", Bin.of(0)));
        checkScan(ref, bytes, bv, all(), "k4 k2 k5 k1 k3");
        checkScan(ref, bytes, bv, q(list(), null, false, null, false, Bin.of(0), true), "k1 k5 k2");
        checkScan(ref, bytes, bv, q(list(Bin.of(0)), null, false, null, false, null, false),
                "k2 k5");
        checkScan(ref, bytes, bv, q(list(), Bin.of(0), false, Bin.of(0xff), false, null, false),
                "k1");
        boolean refused = false;
        try {
            ref.scan(bytes, bv, q(list(Bin.of(0)), Bin.of(0), true, null, false, null, false));
        } catch (IllegalArgumentException e) {
            refused = true;
        }
        check(refused, "a bound after eq on every level");
    }

    static Query all() {
        return q(list(), null, false, null, false, null, false);
    }

    static Query q(List<Object> eq, Object from, boolean fromInclusive, Object to,
            boolean toInclusive, Object prefix, boolean backward) {
        return new Query(eq, from, fromInclusive, to, toInclusive, prefix, backward);
    }

    private static void checkScan(IndexReference ref, Def d, Map<String, Object> values,
            Query q, String expected) {
        StringBuilder got = new StringBuilder();
        for (Entry e : ref.scan(d, values, q)) {
            got.append(got.length() > 0 ? " " : "").append(e.key.substring(e.key.lastIndexOf('/') + 1));
        }
        check(got.toString().equals(expected), q + " on " + d + ": " + got + ", not " + expected);
    }

    /** The model: versions by time, the last write of a key wins, own keys only, any order. */
    @Nano
    public static void testModel() {
        Model m = new Model();
        m.commit(10, Arrays.asList(new Write("/h/a", "1"), new Write("/h/b", "2"),
                new Write("/h/a", "3"), new Write("/h/s/c", "4")));
        m.commit(30, Arrays.asList(new Write("/h/a", null)));
        m.commit(20, Arrays.asList(new Write("/h/b", "5")));
        check("3".equals(m.valueAt("/h/a", 10)) && "3".equals(m.valueAt("/h/a", 29))
                && m.valueAt("/h/a", 30) == null && m.valueAt("/h/a", 9) == null, "valueAt");
        check(m.dirAt("/h/", 25).toString().equals("{/h/a=3, /h/b=5}"), "dirAt " + m.dirAt("/h/", 25));
        check(m.dirAt("/h/s/", 25).keySet().toString().equals("[/h/s/c]"), "dirAt of a subdirectory");
        check(m.lastTime() == 30, "lastTime");
        boolean refused = false;
        try {
            m.commit(20, Arrays.asList(new Write("/h/b", "6")));
        } catch (AssertionError e) {
            refused = true;
        }
        check(refused, "two transactions at one time");
    }

    /** A generation's states from its intervals, and what an observation teaches. */
    @Nano
    public static void testGenerationStates() {
        Model m = new Model();
        Def d = def("/h/", level(Type.LONG, "a"));
        Generation g = m.create(d, 10, 12);
        check(g.stateAt(10) == State.ABSENT && g.stateAt(11) == State.UNKNOWN
                && g.stateAt(12) == State.UNKNOWN && g.stateAt(100) == State.UNKNOWN, "created");
        g.activated.notDoneAt(20);
        check(g.stateAt(12) == State.BUILDING && g.stateAt(20) == State.BUILDING
                && g.stateAt(21) == State.UNKNOWN, "seen building at 20");
        g.activated.doneAt(30);
        check(g.stateAt(30) == State.ACTIVE && g.stateAt(25) == State.UNKNOWN, "seen active at 30");
        boolean refused = false;
        try {
            g.activated.notDoneAt(31);
        } catch (AssertionError e) {
            refused = true;
        }
        check(refused, "building after active");
        check(m.live("i") == g, "live");
        g.deleted.set(40, 41);
        check(g.stateAt(40) == State.ACTIVE && g.stateAt(41) == State.ABSENT && m.live("i") == null,
                "deleted");
        Generation g2 = m.create(d, 50, 51);
        check(m.at("i", 45).isEmpty() && m.at("i", 35).get(0) == g && m.at("i", 60).get(0) == g2,
                "generations of a name");
    }

    /** Each planted fault changes the reference's answer where it should. */
    @Nano
    public static void testPlantedFaults() {
        Def d = def("/h/", level(Type.DOUBLE, "a"));
        TreeMap<String, Object> values = new TreeMap<String, Object>();
        values.put("/h/k1", obj("a", -0.0));
        values.put("/h/k2", obj("a", 1.0));
        Query eqZero = q(list(0.0), null, false, null, false, null, false);
        Query above = q(list(), 1.0, false, null, false, null, false);
        IndexReference ok = new IndexReference();
        check(ok.scan(d, values, eqZero).size() == 1 && ok.scan(d, values, above).isEmpty(), "ok");
        IndexReference zero = new IndexReference(Fault.NEG_ZERO_APART);
        check(zero.scan(d, values, eqZero).isEmpty(), "NEG_ZERO_APART");
        IndexReference bound = new IndexReference(Fault.BOUND_OFF_BY_ONE);
        check(bound.scan(d, values, above).size() == 1, "BOUND_OFF_BY_ONE");

        Model m = new Model();
        m.commit(5, Arrays.asList(new Write("/h/k1", obj("a", 3.0))));
        Generation g = m.create(d, 6, 7);
        m.commit(8, Arrays.asList(new Write("/h/k1", obj("a", 4.0))));
        m.commit(9, Arrays.asList(new Write("/h/k1", obj("a", 5.0))));
        check(ok.expectedEntries(m, g, 9).toString().equals("[[5.0] \"/h/k1\"]"),
                "expected " + ok.expectedEntries(m, g, 9));
        IndexReference kept = new IndexReference(Fault.ENTRY_NOT_DELETED);
        check(kept.expectedEntries(m, g, 9).toString()
                .equals("[[3.0] \"/h/k1\", [4.0] \"/h/k1\", [5.0] \"/h/k1\"]"),
                "ENTRY_NOT_DELETED " + kept.expectedEntries(m, g, 9));
        check(kept.expectedEntries(m, g, 8).size() == 2, "ENTRY_NOT_DELETED at 8");
    }
}
