package bergdb.pubimp;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.TreeMap;

import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.DatabaseBuilder;
import bergdb.pub.Duration;
import bergdb.pub.Factory;
import bergdb.pub.IndexAlreadyExistsException;
import bergdb.pub.IndexBuilder;
import bergdb.pub.Kv;
import bergdb.pub.NoSuchIndexException;
import bergdb.pub.TestClock;
import bergdb.pub.Time;
import bergdb.pub.Transaction;
import bergdb.pub.UseIndexBuilder;
import bergdb.pub.WBuilder;
import bergdb.pub.util.Job;
import bergdb.pub.util.JobStatus;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.stream.MemoryStream;
import bergdb.pubimp.IndexReference.Bin;
import bergdb.pubimp.IndexReference.Call;
import bergdb.pubimp.IndexReference.Def;
import bergdb.pubimp.IndexReference.Entry;
import bergdb.pubimp.IndexReference.Fault;
import bergdb.pubimp.IndexReference.Generation;
import bergdb.pubimp.IndexReference.Level;
import bergdb.pubimp.IndexReference.Model;
import bergdb.pubimp.IndexReference.Query;
import bergdb.pubimp.IndexReference.State;
import bergdb.pubimp.IndexReference.Type;
import bergdb.pubimp.IndexReference.Write;

/**
 * Harness H2 of the user indexes: an index is a function of the data (bergdb 020-10, section
 * 9.1), against IndexReference. This class holds the harness's generators, by a seed: the
 * data (objects with fields of every kind and their edges, Strings and byte[]s), the index
 * definitions (1 to 3 levels, the four types, nested paths, the three ways to give a path),
 * the operations (transactions of puts and deletes in w() and rw(), creations, a creation
 * of a used name, deletions, joins, restarts) and the scans of a check (every eq prefix of
 * an entry's levels, a bound pair, a prefix, each direction). simulate() runs them against
 * the reference alone, with a database of exact times, to check the generators and to show
 * that the checks find each planted fault (Fault). The run against BergDB uses the API of
 * bergdb 020-10, section 3, and joins this class with it.
 */
final class IndexHarness {

    // ======== The operations ========

    /** An operation of a run. */
    abstract static class Op {
    }

    /** A transaction of puts and deletes, in rw() or in w(). */
    static final class Tx extends Op {
        final boolean rw;
        final List<Write> writes;

        Tx(boolean rw, List<Write> writes) {
            this.rw = rw;
            this.writes = writes;
        }

        public String toString() {
            return (rw ? "rw " : "w ") + writes;
        }
    }

    /**
     * A creation of an index; with join, start().join() waits for its build. Of a name in
     * use, it must throw IndexAlreadyExistsException.
     */
    static final class Create extends Op {
        final Def def;
        final boolean join;

        Create(Def def, boolean join) {
            this.def = def;
            this.join = join;
        }

        public String toString() {
            return "create " + def + (join ? ", join" : "");
        }
    }

    /** A deletion; of a name not in use, it must throw NoSuchIndexException. */
    static final class DeleteIndex extends Op {
        final String name;

        DeleteIndex(String name) {
            this.name = name;
        }

        public String toString() {
            return "delete index " + IndexReference.show(name);
        }
    }

    /** Waits for the build of a live index: indexJob(name).join(). */
    static final class Join extends Op {
        final String name;

        Join(String name) {
            this.name = name;
        }

        public String toString() {
            return "join " + IndexReference.show(name);
        }
    }

    /** A stop and a start of the database. */
    static final class Restart extends Op {
        public String toString() {
            return "restart";
        }
    }

    // ======== The generators ========

    /** The two directories, the second inside the first (S2-F16). */
    static final String[] DIRS = {"/h/a/", "/h/a/sub/"};

    /** The names of object keys, in each directory: no suffix, one .obj. */
    static final String[] OBJECT_NAMES = {"k0", "k1", "k2", "k3", "k4", "k5", "k6", "k7", "k8",
            "k9", "k10", "k11", "kå", "k￿", "k😀", "k3.obj"};

    /** The names of keys with a suffix: a String at .txt, a byte[] at .bin. */
    static final String[] OTHER_NAMES = {"t.txt", "u.bin"};

    /** Index names; "primary" is a name like any other (bergdb 020-10, section 3.2). */
    static final String[] INDEX_NAMES = {"i0", "i1", "i2", "primary", "ä"};

    /** An object's top-level fields; "x.y" is one name with a '.'. */
    static final String[] TOP_FIELDS = {"a", "b", "c", "x.y"};

    /** The paths of the levels: the last nine find values, "n" an object, "q" nothing. */
    static final String[][] PATHS = {{"a"}, {"b"}, {"c"}, {"x.y"}, {"n", "a"}, {"n", "c"},
            {"n", "x.y"}, {"n", "m", "a"}, {"n", "m", "c"}, {"n"}, {"q"}};

    static final long[] LONGS = {Long.MIN_VALUE, Long.MIN_VALUE + 1, -4294967296L,
            Integer.MIN_VALUE, -129, -1, 0, 1, 127, 128, 255, 65536, Integer.MAX_VALUE,
            4294967296L, Long.MAX_VALUE - 1, Long.MAX_VALUE};

    static final double[] DOUBLES = {-0.0, 0.0, Double.NaN, Double.POSITIVE_INFINITY,
            Double.NEGATIVE_INFINITY, Double.MIN_VALUE, -Double.MIN_VALUE, Double.MAX_VALUE,
            -Double.MAX_VALUE, 1e-300, -1e300, Double.longBitsToDouble(0x7ff0000000000001L),
            Double.longBitsToDouble(0xfff8000000000000L)};

    static final double[] SMALL_DOUBLES = {-0.0, 0.0, 1.0, -1.0, 0.5, 2.0};

    static final String[] STRINGS = {"", "a", "b", "ab", "a\u0000", "\u0000", "\u0001",
            "a\u0001b", "é", "￿", "😀", "a😀", "𐀀",
            "\u007f", "\u0080"};

    /** Strings at and around the 4,096 bytes of levels (bergdb 020-10, section 3.3). */
    static final String[] LONG_STRINGS = {IndexReference.repeat("a", 4087),
            IndexReference.repeat("a", 4088), IndexReference.repeat("a", 4095),
            IndexReference.repeat("a", 4096), IndexReference.repeat("\u0000", 2047),
            IndexReference.repeat("\u0000", 2048), IndexReference.repeat("a", 2040)};

    /** The code points of random strings. */
    static final int[] CODE_POINTS = {'a', 'b', 0, 1, 0xe9, 0xffff, 0x1f600};

    static final int[][] BYTES = {{}, {0}, {1}, {0, 1}, {1, 0}, {0xff}, {0x7f}, {0x80}, {0, 0},
            {1, 1}, {2}, {0xff, 0}};

    /** The bytes of random byte[]s: never 0x82 or format 1's "bergo" first. */
    static final int[] BYTE_VALUES = {0, 1, 2, 0x7f, 0x80, 0xff};

    /** byte[] values that start with format 2's header and fail its check: not objects. */
    static final Bin[] NOT_OBJECTS = {Bin.of(0x82), Bin.of(0x82, 0xff)};

    /** The type whose kind a field holds most often, by its name (the path's last part). */
    static Type preferred(String name) {
        switch (name) {
        case "a":
            return Type.LONG;
        case "b":
            return Type.DOUBLE;
        case "c":
            return Type.STRING;
        default:
            return Type.BYTES;
        }
    }

    static long longValue(Random r) {
        int k = r.nextInt(10);
        if (k < 6) {
            return r.nextInt(6) - 2;
        } else if (k < 9) {
            return LONGS[r.nextInt(LONGS.length)];
        }
        return r.nextLong();
    }

    static double doubleValue(Random r) {
        int k = r.nextInt(10);
        if (k < 5) {
            return SMALL_DOUBLES[r.nextInt(SMALL_DOUBLES.length)];
        } else if (k < 9) {
            return DOUBLES[r.nextInt(DOUBLES.length)];
        }
        return r.nextGaussian() * 1e6;
    }

    static String stringValue(Random r) {
        int k = r.nextInt(100);
        if (k < 50) {
            return STRINGS[r.nextInt(STRINGS.length)];
        } else if (k < 99) {
            StringBuilder s = new StringBuilder();
            for (int i = r.nextInt(5); i > 0; i--) {
                s.appendCodePoint(CODE_POINTS[r.nextInt(CODE_POINTS.length)]);
            }
            return s.toString();
        }
        return LONG_STRINGS[r.nextInt(LONG_STRINGS.length)];
    }

    static Bin bytesValue(Random r) {
        if (r.nextBoolean()) {
            return Bin.of(BYTES[r.nextInt(BYTES.length)]);
        }
        int[] b = new int[r.nextInt(5)];
        for (int i = 0; i < b.length; i++) {
            b[i] = BYTE_VALUES[r.nextInt(BYTE_VALUES.length)];
        }
        return Bin.of(b);
    }

    /** A value of the type's kind, not NaN: for a scan's arguments. */
    static Object typed(Type t, Random r) {
        switch (t) {
        case LONG:
            return longValue(r);
        case DOUBLE:
            double d = doubleValue(r);
            return Double.isNaN(d) ? 1.0 : d;
        case STRING:
            return stringValue(r);
        default:
            return bytesValue(r);
        }
    }

    /** A field's value: the kind that its name prefers, seven times in ten, else any kind. */
    static Object field(String name, Random r) {
        if (r.nextInt(10) < 7) {
            return typed(preferred(name), r);
        }
        int k = r.nextInt(100);
        if (k < 30) {
            return longValue(r);
        } else if (k < 50) {
            return doubleValue(r);
        } else if (k < 70) {
            return stringValue(r);
        } else if (k < 85) {
            return bytesValue(r);
        } else if (k < 90) {
            return r.nextBoolean();
        } else if (k < 95) {
            List<Object> a = new ArrayList<Object>();
            for (int i = r.nextInt(3); i > 0; i--) {
                a.add(longValue(r));
            }
            return a;
        }
        return IndexReference.obj("a", longValue(r));
    }

    /**
     * An object: each top-level field present four times in five; the object "n" (with "m"
     * in it) or another value at "n", or none; now and then a field that no index uses.
     */
    static TreeMap<String, Object> object(Random r) {
        TreeMap<String, Object> o = new TreeMap<String, Object>();
        for (String f : TOP_FIELDS) {
            if (r.nextInt(5) != 0) {
                o.put(f, field(f, r));
            }
        }
        int n = r.nextInt(10);
        if (n < 6) {
            o.put("n", nested(r, true));
        } else if (n < 7) {
            o.put("n", field("n", r));
        }
        if (r.nextInt(10) == 0) {
            o.put("z", field("z", r));
        }
        return o;
    }

    private static TreeMap<String, Object> nested(Random r, boolean withM) {
        TreeMap<String, Object> o = new TreeMap<String, Object>();
        for (String f : new String[] {"a", "c", "x.y"}) {
            if (r.nextInt(5) != 0) {
                o.put(f, field(f, r));
            }
        }
        if (withM && r.nextBoolean()) {
            o.put("m", r.nextInt(5) != 0 ? nested(r, false) : field("m", r));
        }
        return o;
    }

    /**
     * A value to put at key: at an object key an object, a String, a byte[], or bytes that
     * are not an object; at .txt a String, at .bin a byte[].
     */
    static Object keyValue(String key, Random r) {
        if (key.endsWith(".txt")) {
            return stringValue(r);
        } else if (key.endsWith(".bin")) {
            return bytesValue(r);
        }
        int k = r.nextInt(100);
        if (k < 75) {
            return object(r);
        } else if (k < 85) {
            return stringValue(r);
        } else if (k < 95) {
            return bytesValue(r);
        }
        return NOT_OBJECTS[r.nextInt(NOT_OBJECTS.length)];
    }

    static String key(Random r) {
        String dir = r.nextInt(5) != 0 ? DIRS[0] : DIRS[1];
        return dir + (r.nextInt(10) != 0 ? OBJECT_NAMES[r.nextInt(OBJECT_NAMES.length)]
                : OTHER_NAMES[r.nextInt(OTHER_NAMES.length)]);
    }

    /** An index's definition: 1 to 3 levels, mostly of the type that the field prefers. */
    static Def def(String name, Random r) {
        String dir = r.nextInt(10) < 7 ? DIRS[0] : DIRS[1];
        List<Level> levels = new ArrayList<Level>();
        for (int i = 1 + r.nextInt(3); i > 0; i--) {
            String[] path = r.nextInt(100) < 85 ? PATHS[r.nextInt(9)] : PATHS[9 + r.nextInt(2)];
            Type type = r.nextInt(4) != 0 ? preferred(path[path.length - 1])
                    : Type.values()[r.nextInt(4)];
            levels.add(new Level(type, call(path, r), path));
        }
        return new Def(name, dir, levels);
    }

    /** How the path is given: field() for one part, else nestedField() of a String or parts. */
    private static Call call(String[] path, Random r) {
        boolean dotted = false;
        for (String part : path) {
            dotted |= part.indexOf('.') >= 0;
        }
        int k = r.nextInt(10);
        if (path.length == 1) {
            return k < 7 ? Call.FIELD : !dotted && k < 9 ? Call.NESTED_STRING : Call.NESTED_ARRAY;
        }
        return dotted || k < 4 ? Call.NESTED_ARRAY : Call.NESTED_STRING;
    }

    /**
     * A generator of a run's operations by its seed. Its choices depend on the seed and on the
     * model's names in use, which the operations alone decide, not on a build's timing: so a
     * seed gives the same operations at every run.
     */
    static final class Generator {
        final Random r;
        /** The deletion that follows a creation without join one time in four, or null. */
        private Op next;

        Generator(long seed) {
            r = new Random(seed);
        }

        Op op(Model m, boolean restarts) {
            if (next != null) {
                Op op = next;
                next = null;
                return op;
            }
            int k = r.nextInt(100);
            if (k < 72) {
                return tx();
            } else if (k < 82) {
                return create(m);
            } else if (k < 87) {
                return deleteIndex(m);
            } else if (k < 95) {
                List<Generation> live = live(m);
                if (!live.isEmpty()) {
                    return new Join(live.get(r.nextInt(live.size())).def.name);
                }
            } else if (k < 97 && restarts) {
                return new Restart();
            }
            return tx();
        }

        Tx tx() {
            List<Write> writes = new ArrayList<Write>();
            for (int i = 1 + r.nextInt(4); i > 0; i--) {
                String key = key(r);
                writes.add(new Write(key, r.nextInt(5) != 0 ? keyValue(key, r) : null));
            }
            return new Tx(r.nextBoolean(), writes);
        }

        /** A creation: of a name in use one time in five, else of a free name if there is one. */
        Create create(Model m) {
            List<Generation> live = live(m);
            List<String> free = new ArrayList<String>();
            for (String name : INDEX_NAMES) {
                if (m.live(name) == null) {
                    free.add(name);
                }
            }
            String name;
            if (!live.isEmpty() && (free.isEmpty() || r.nextInt(5) == 0)) {
                name = live.get(r.nextInt(live.size())).def.name;
            } else {
                name = free.get(r.nextInt(free.size()));
            }
            Create c = new Create(def(name, r), r.nextInt(10) < 6);
            if (!c.join && r.nextInt(4) == 0) {
                // A deletion at once, while the build likely runs.
                next = new DeleteIndex(name);
            }
            return c;
        }

        /** A deletion: of a name in use four times in five, else of any name. */
        DeleteIndex deleteIndex(Model m) {
            List<Generation> live = live(m);
            if (!live.isEmpty() && r.nextInt(5) != 0) {
                return new DeleteIndex(live.get(r.nextInt(live.size())).def.name);
            }
            return new DeleteIndex(INDEX_NAMES[r.nextInt(INDEX_NAMES.length)]);
        }

        private static List<Generation> live(Model m) {
            List<Generation> live = new ArrayList<Generation>();
            for (Generation g : m.generations) {
                if (!g.isDeleted()) {
                    live.add(g);
                }
            }
            return live;
        }
    }

    /**
     * The scans of a check of an index whose entries are given (bergdb 020-10, section 9.1):
     * from a random entry's levels (random values if there is none), for each k from 0 to n,
     * eq on its first k levels; and if k < n, on level k + 1 a bound pair (each inclusive or
     * not, one of them now and then left out; a level's value of the entries that match eq
     * three times in five, so that a bound meets a value) and, for a string or bytes level,
     * a prefix of the entry's value (or a random one). Each in a random direction; a 0.0
     * given as -0.0 one time in two.
     */
    static List<Query> queries(Def def, List<Entry> entries, Random r) {
        int n = def.levels.size();
        List<Object> base;
        if (entries.isEmpty()) {
            base = new ArrayList<Object>();
            for (int i = 0; i < n; i++) {
                base.add(typed(def.type(i), r));
            }
        } else {
            base = entries.get(r.nextInt(entries.size())).levels;
        }
        List<Query> result = new ArrayList<Query>();
        for (int k = 0; k <= n; k++) {
            List<Object> eq = new ArrayList<Object>();
            for (int i = 0; i < k; i++) {
                eq.add(argument(base.get(i), r));
            }
            result.add(new Query(eq, null, false, null, false, null, r.nextBoolean()));
            if (k == n) {
                break;
            }
            Type t = def.type(k);
            Object from = r.nextInt(5) == 0 ? null : bound(def, k, base, entries, r);
            Object to = r.nextInt(5) == 0 ? null : bound(def, k, base, entries, r);
            if (from == null && to == null) {
                from = bound(def, k, base, entries, r);
            }
            result.add(new Query(eq, from, r.nextBoolean(), to, r.nextBoolean(), null,
                    r.nextBoolean()));
            if (t == Type.STRING || t == Type.BYTES) {
                result.add(new Query(eq, null, false, null, false, prefix(base.get(k), r),
                        r.nextBoolean()));
            }
        }
        return result;
    }

    /** A level value as a scan's argument: 0.0 as -0.0 one time in two. */
    private static Object argument(Object v, Random r) {
        if (v instanceof Double && (Double) v == 0.0 && r.nextBoolean()) {
            return -0.0;
        }
        return v;
    }

    /** A bound on level k: a value of an entry that matches base on the levels before k, or random. */
    private static Object bound(Def def, int k, List<Object> base, List<Entry> entries, Random r) {
        if (!entries.isEmpty() && r.nextInt(5) < 3) {
            List<Object> values = new ArrayList<Object>();
            for (Entry e : entries) {
                if (e.levels.subList(0, k).equals(base.subList(0, k))) {
                    values.add(e.levels.get(k));
                }
            }
            if (values.isEmpty()) {
                values.add(entries.get(r.nextInt(entries.size())).levels.get(k));
            }
            return argument(values.get(r.nextInt(values.size())), r);
        }
        return typed(def.type(k), r);
    }

    /** A prefix of v (a String by code points, or a Bin), or one time in five a random one. */
    private static Object prefix(Object v, Random r) {
        if (v instanceof String) {
            if (r.nextInt(5) == 0) {
                return stringValue(r);
            }
            String s = (String) v;
            int c = r.nextInt(s.codePointCount(0, s.length()) + 1);
            return s.substring(0, s.offsetByCodePoints(0, c));
        }
        if (r.nextInt(5) == 0) {
            return bytesValue(r);
        }
        Bin b = (Bin) v;
        return b.prefix(r.nextInt(b.length() + 1));
    }

    // ======== A run against the reference alone ========

    /** Counts of what a simulated run did and saw, by name; the operations' text. */
    static final class Stats {
        final TreeMap<String, Integer> counts = new TreeMap<String, Integer>();
        final StringBuilder ops = new StringBuilder();

        void add(String name) {
            add(name, 1);
        }

        void add(String name, int n) {
            Integer c = counts.get(name);
            counts.put(name, (c == null ? 0 : c) + n);
        }

        int get(String name) {
            Integer c = counts.get(name);
            return c == null ? 0 : c;
        }

        void addAll(Stats s) {
            for (Map.Entry<String, Integer> e : s.counts.entrySet()) {
                add(e.getKey(), e.getValue());
            }
        }
    }

    /** The planted faults, each in its own reference. */
    static final Fault[] FAULTS = {Fault.ENTRY_NOT_DELETED, Fault.BOUND_OFF_BY_ONE,
            Fault.NEG_ZERO_APART};

    /**
     * Runs the operations of seed against the references alone: a database of exact times,
     * in which a creation without join ends its build at a random later operation. After
     * each operation, at the latest time and at two past times, for each index active there:
     * each scan of queries() is in the grammar, and its result is the entries that match it,
     * in order; and for each planted fault, counts the checks where that reference differs
     * from the correct one, by the entries (as a harness compares the raw entries, stale ones
     * included) or by a scan's result (as it compares kvs(): a scan skips a stale entry, so
     * it is over f of the values at t). Returns the counts.
     */
    static Stats simulate(long seed, int steps) {
        Stats stats = new Stats();
        Generator gen = new Generator(seed);
        Model m = new Model();
        IndexReference ok = new IndexReference();
        IndexReference[] faulty = new IndexReference[FAULTS.length];
        for (int i = 0; i < FAULTS.length; i++) {
            faulty[i] = new IndexReference(FAULTS[i]);
        }
        Random building = new Random(seed + 1);
        long time = 1;
        for (int step = 0; step < steps; step++) {
            Op op = gen.op(m, true);
            stats.ops.append(op).append('\n');
            if (op instanceof Tx) {
                Tx tx = (Tx) op;
                m.commit(++time, tx.writes);
                count(stats, tx);
            } else if (op instanceof Create) {
                Create c = (Create) op;
                if (m.live(c.def.name) != null) {
                    stats.add("create of a used name");
                } else {
                    Generation g = m.create(c.def, time, ++time);
                    if (c.join) {
                        g.activated.set(time, ++time);
                    }
                    count(stats, c.def);
                }
            } else if (op instanceof DeleteIndex) {
                Generation g = m.live(((DeleteIndex) op).name);
                if (g == null) {
                    stats.add("delete of a free name");
                } else {
                    g.deleted.set(time, ++time);
                    stats.add(g.activated.hi == Long.MAX_VALUE ? "delete index while building"
                            : "delete index");
                }
            } else if (op instanceof Join) {
                Generation g = m.live(((Join) op).name);
                if (g.activated.hi == Long.MAX_VALUE) {
                    g.activated.set(time, ++time);
                }
                stats.add("join");
            } else {
                stats.add("restart");
            }
            for (Generation g : m.generations) {
                if (!g.isDeleted() && g.activated.hi == Long.MAX_VALUE) {
                    if (building.nextInt(3) == 0) {
                        g.activated.set(time, ++time);
                    } else {
                        g.activated.notDoneAt(time);
                    }
                }
            }

            Random cr = new Random(seed * 1000003 + step);
            check(m, time, ok, faulty, cr, stats);
            for (int i = 0; i < 2 && m.times.size() > 1; i++) {
                List<Long> times = new ArrayList<Long>(m.times);
                check(m, times.get(cr.nextInt(times.size())), ok, faulty, cr, stats);
            }
        }
        return stats;
    }

    /** The checks at t of every index active at t. */
    private static void check(Model m, long t, IndexReference ok, IndexReference[] faulty,
            Random r, Stats stats) {
        for (Generation g : m.generations) {
            State state = g.stateAt(t);
            if (state != State.ACTIVE) {
                stats.add("state " + state);
                continue;
            }
            Def def = g.def;
            Map<String, Object> values = m.dirAt(def.dir, t);
            List<Entry> entries = ok.entries(def, values);
            if (!ok.expectedEntries(m, g, t).equals(entries)) {
                throw new AssertionError("expectedEntries is not entries: " + def + " at " + t);
            }
            List<List<Entry>> faultyEntries = new ArrayList<List<Entry>>();
            for (int i = 0; i < faulty.length; i++) {
                if (!faulty[i].expectedEntries(m, g, t).equals(entries)) {
                    stats.add("found by the entries: " + faulty[i].fault);
                }
                faultyEntries.add(faulty[i].entries(def, values));
            }
            stats.add("checks");
            stats.add("entries", entries.size());
            for (Query q : queries(def, entries, r)) {
                List<Entry> result = ok.filter(def, entries, q);
                checkResult(def, entries, q, result);
                count(stats, def, q, entries, result);
                for (int i = 0; i < faulty.length; i++) {
                    List<Entry> fr = faulty[i].filter(def, faultyEntries.get(i), q);
                    if (!keys(fr).equals(keys(result))) {
                        stats.add("found by a scan: " + faulty[i].fault);
                    }
                }
            }
        }
    }

    private static List<String> keys(List<Entry> entries) {
        List<String> keys = new ArrayList<String>();
        for (Entry e : entries) {
            keys.add(e.key);
        }
        return keys;
    }

    /** A scan's result: the entries that match, each once, in the order or backward. */
    private static void checkResult(Def def, List<Entry> entries, Query q, List<Entry> result) {
        int last = -1;
        for (Entry e : result) {
            int i = entries.indexOf(e);
            if (i < 0 || (q.backward ? last >= 0 && i >= last : i <= last)) {
                throw new AssertionError("the scan " + q + " on " + def + " gave " + e
                        + " out of order or not an entry");
            }
            last = i;
        }
    }

    private static void count(Stats stats, Tx tx) {
        stats.add(tx.rw ? "rw" : "w");
        for (Write w : tx.writes) {
            if (w.value == null) {
                stats.add("delete");
                continue;
            }
            stats.add(w.key.startsWith(DIRS[1]) ? "put in the subdirectory" : "put");
            if (!IndexReference.isObjectKey(w.key)) {
                stats.add("put at a suffix");
            } else if (w.value instanceof String) {
                stats.add("String at an object key");
            } else if (w.value instanceof Bin) {
                stats.add(((Bin) w.value).length() > 0 && ((Bin) w.value).bytes()[0] == (byte) 0x82
                        ? "bytes not an object" : "byte[] at an object key");
            } else {
                Map<?, ?> o = (Map<?, ?>) w.value;
                for (String f : TOP_FIELDS) {
                    if (!o.containsKey(f)) {
                        stats.add("absent field");
                    }
                }
                countValues(stats, o);
            }
        }
    }

    private static void countValues(Stats stats, Object v) {
        if (v instanceof Map) {
            for (Object x : ((Map<?, ?>) v).values()) {
                if (x instanceof Map) {
                    stats.add("nested object");
                }
                countValues(stats, x);
            }
        } else if (v instanceof Double) {
            double d = (Double) v;
            if (Double.isNaN(d)) {
                stats.add("NaN");
            } else if (Double.isInfinite(d)) {
                stats.add(d > 0 ? "+inf" : "-inf");
            } else if (d == 0.0 && 1 / d < 0) {
                stats.add("-0.0");
            }
        } else if (v instanceof String) {
            String s = (String) v;
            if (s.indexOf('\u0000') >= 0) {
                stats.add("string with 00");
            }
            if (s.indexOf('\u0001') >= 0) {
                stats.add("string with 01");
            }
            if (s.codePointCount(0, s.length()) < s.length()) {
                stats.add("string with an astral char");
            }
            if (s.length() > 2000) {
                stats.add("long string");
            }
        } else if (v instanceof Bin) {
            for (byte b : ((Bin) v).bytes()) {
                stats.add(b == 0 ? "bytes with 00" : b == 1 ? "bytes with 01"
                        : b == (byte) 0xff ? "bytes with ff" : "bytes with another");
            }
        } else if (v instanceof Boolean) {
            stats.add("boolean");
        } else if (v instanceof List) {
            stats.add("array");
        }
    }

    private static void count(Stats stats, Def def) {
        stats.add("levels " + def.levels.size());
        stats.add("index on " + def.dir);
        for (Level l : def.levels) {
            stats.add("type " + l.type);
            stats.add("call " + l.call);
            if (l.path.length > 1) {
                stats.add("nested path");
            }
            if (l.path[l.path.length - 1].indexOf('.') >= 0) {
                stats.add("a name with a dot");
            }
        }
    }

    private static final IndexReference OK = new IndexReference();

    private static void count(Stats stats, Def def, Query q, List<Entry> entries,
            List<Entry> result) {
        stats.add("scans");
        stats.add(result.isEmpty() ? "empty scan" : "scan with results");
        if (q.backward) {
            stats.add("backward");
        }
        if (q.prefix != null && !result.isEmpty()) {
            stats.add("prefix with results");
        }
        for (Object v : q.eq) {
            if (v instanceof Double && (Double) v == 0.0 && 1 / (Double) v < 0) {
                stats.add("-0.0 as an argument");
            }
        }
        if (q.from != null && !q.fromInclusive) {
            // An exclusive lower bound equal to a value of the level, among the entries that
            // match the eq levels: where an off-by-one bound shows.
            int k = q.rangeLevel();
            Query eqOnly = new Query(q.eq, null, false, null, false, null, false);
            for (Entry e : entries) {
                if (OK.matches(def, eqOnly, e.levels)
                        && IndexReference.compareLevel(def.type(k), e.levels.get(k), q.from) == 0) {
                    stats.add("exclusive bound on a value");
                    break;
                }
            }
        }
        if (q.from != null && q.to != null
                && IndexReference.compareLevel(def.type(q.rangeLevel()), q.from, q.to) > 0) {
            stats.add("from above to");
        }
    }

    // ======== Tests ========

    private static void check(boolean ok, String message) {
        if (!ok) {
            throw new AssertionError(message);
        }
    }

    /**
     * The generators against the reference alone, 4 seeds of 400 operations: every scan is
     * in the grammar and gives the entries that match in order; the data, the definitions,
     * the operations and the scans cover what bergdb 020-10, section 9.1, lists; each planted
     * fault is found; a seed gives the same operations twice.
     */
    @Nano
    public static void testGenerators() {
        Stats all = new Stats();
        for (long seed = 1; seed <= 4; seed++) {
            all.addAll(simulate(seed, 400));
        }
        String[] covered = {"rw", "w", "delete", "put in the subdirectory", "put at a suffix",
                "String at an object key", "byte[] at an object key", "bytes not an object",
                "absent field", "nested object", "NaN", "+inf", "-inf", "-0.0", "string with 00",
                "string with 01", "string with an astral char", "long string", "bytes with 00",
                "bytes with 01", "bytes with ff", "boolean", "array", "levels 1", "levels 2",
                "levels 3", "index on /h/a/", "index on /h/a/sub/", "type LONG", "type DOUBLE",
                "type STRING", "type BYTES", "call FIELD", "call NESTED_STRING",
                "call NESTED_ARRAY", "nested path", "a name with a dot", "create of a used name",
                "delete of a free name", "delete index", "delete index while building", "join", "restart",
                "state BUILDING", "state ABSENT", "scan with results", "empty scan", "backward",
                "prefix with results", "-0.0 as an argument", "exclusive bound on a value",
                "from above to"};
        for (String c : covered) {
            check(all.get(c) > 0, "the generators never made: " + c + "; " + all.counts);
        }
        for (Fault f : FAULTS) {
            check(all.get("found by the entries: " + f) + all.get("found by a scan: " + f) > 0,
                    "the planted fault " + f + " is not found; " + all.counts);
        }
        check(all.get("found by a scan: " + Fault.ENTRY_NOT_DELETED) == 0,
                "a scan skips stale entries: only the raw entries show ENTRY_NOT_DELETED");
        check(simulate(7, 100).ops.toString().equals(simulate(7, 100).ops.toString()),
                "a seed gives the same operations");
    }

    /** queries() keeps the grammar for every definition, with entries or none. */
    @Nano
    public static void testQueriesInGrammar() {
        Random r = new Random(5);
        IndexReference ok = new IndexReference();
        for (int i = 0; i < 300; i++) {
            Def def = def("i", r);
            List<Entry> entries = new ArrayList<Entry>();
            if (r.nextBoolean()) {
                TreeMap<String, Object> values = new TreeMap<String, Object>();
                for (String name : OBJECT_NAMES) {
                    values.put(def.dir + name, object(r));
                }
                entries = ok.entries(def, values);
            }
            for (Query q : queries(def, entries, r)) {
                q.check(def);
            }
        }
    }

    // ======== The reference against section 4.4's bytes ========

    /** A level's bytes by bergdb 020-10, section 4.4, written here from its text. */
    static byte[] levelBytes(Type t, Object v) {
        switch (t) {
        case LONG:
            return longBytes((Long) v);
        case DOUBLE:
            long x = Double.doubleToLongBits((Double) v);
            return longBytes(x >= 0 ? x : -(x & 0x7fffffffffffffffL));
        case STRING:
            return escaped(((String) v).getBytes(java.nio.charset.StandardCharsets.UTF_8), true);
        default:
            return escaped(((Bin) v).bytes(), true);
        }
    }

    private static byte[] longBytes(long v) {
        byte[] b = new byte[8];
        long u = v ^ 0x8000000000000000L;
        for (int i = 0; i < 8; i++) {
            b[i] = (byte) (u >>> (56 - 8 * i));
        }
        return b;
    }

    /** E: 00 as 01 01, 01 as 01 02, every other byte as it is; then 00 if terminated. */
    private static byte[] escaped(byte[] b, boolean terminated) {
        java.io.ByteArrayOutputStream out = new java.io.ByteArrayOutputStream();
        for (byte x : b) {
            if (x == 0 || x == 1) {
                out.write(1);
                out.write(x + 1);
            } else {
                out.write(x);
            }
        }
        if (terminated) {
            out.write(0);
        }
        return out.toByteArray();
    }

    /** The least byte string above every string that starts with x; null if none. */
    private static byte[] succ(byte[] x) {
        int n = x.length;
        while (n > 0 && x[n - 1] == (byte) 0xff) {
            n--;
        }
        if (n == 0) {
            return null;
        }
        byte[] s = Arrays.copyOf(x, n);
        s[n - 1]++;
        return s;
    }

    private static byte[] concat(byte[]... parts) {
        java.io.ByteArrayOutputStream out = new java.io.ByteArrayOutputStream();
        for (byte[] p : parts) {
            out.write(p, 0, p.length);
        }
        return out.toByteArray();
    }

    /** An entry's bytes after its generation's prefix: the levels, then K (each byte + 2). */
    private static byte[] entryBytes(Def def, Entry e) {
        byte[] levels = new byte[0];
        for (int i = 0; i < def.levels.size(); i++) {
            levels = concat(levels, levelBytes(def.type(i), e.levels.get(i)));
        }
        byte[] name = ("-" + e.key.substring(def.dir.length()))
                .getBytes(java.nio.charset.StandardCharsets.UTF_8);
        for (int i = 0; i < name.length; i++) {
            name[i] += 2;
        }
        return concat(levels, name);
    }

    /** The scan's range [start, end) by section 4.4 (end null: no end). */
    private static byte[][] range(Def def, Query q) {
        byte[] base = new byte[0];
        for (int i = 0; i < q.eq.size(); i++) {
            base = concat(base, levelBytes(def.type(i), q.eq.get(i)));
        }
        byte[] start = base;
        byte[] end = succ(base);
        Type t = q.hasRange() ? def.type(q.rangeLevel()) : null;
        if (q.from != null) {
            byte[] b = concat(base, levelBytes(t, q.from));
            start = q.fromInclusive ? b : succ(b);
        }
        if (q.to != null) {
            byte[] b = concat(base, levelBytes(t, q.to));
            end = q.toInclusive ? succ(b) : b;
        }
        if (q.prefix != null) {
            byte[] p = q.prefix instanceof String
                    ? ((String) q.prefix).getBytes(java.nio.charset.StandardCharsets.UTF_8)
                    : ((Bin) q.prefix).bytes();
            start = concat(base, escaped(p, false));
            end = succ(start);
        }
        return new byte[][] {start, end};
    }

    /**
     * The reference's order and scans (Java values) against section 4.4's encodings and
     * ranges (bytes), two formulations of one meaning: on generated definitions, values and
     * scans, the entries sorted by their bytes are the reference's order, and the entries
     * whose bytes are in a scan's range are its result.
     */
    @Nano
    public static void testReferenceAgainstSection44() {
        Random r = new Random(11);
        IndexReference ok = new IndexReference();
        for (int round = 0; round < 300; round++) {
            final Def def = def("i", r);
            TreeMap<String, Object> values = new TreeMap<String, Object>();
            for (String name : OBJECT_NAMES) {
                values.put(def.dir + name, object(r));
            }
            List<Entry> entries = ok.entries(def, values);
            List<Entry> byBytes = new ArrayList<Entry>(entries);
            byBytes.sort((a, b) -> Arrays.compareUnsigned(entryBytes(def, a), entryBytes(def, b)));
            check(byBytes.equals(entries), "the order of " + def + ": " + entries + ", by bytes "
                    + byBytes);
            for (Query q : queries(def, entries, r)) {
                byte[][] range = range(def, q);
                List<Entry> selected = new ArrayList<Entry>();
                for (Entry e : entries) {
                    byte[] b = entryBytes(def, e);
                    if (Arrays.compareUnsigned(range[0], b) <= 0
                            && (range[1] == null || Arrays.compareUnsigned(b, range[1]) < 0)) {
                        selected.add(e);
                    }
                }
                List<Entry> result = ok.filter(def, entries, q);
                if (q.backward) {
                    java.util.Collections.reverse(selected);
                }
                check(selected.equals(result), q + " on " + def + ": " + result + ", by bytes "
                        + selected);
            }
        }
    }

    /** The values that the generators make are in the model's kinds. */
    @Nano
    public static void testValueKinds() {
        Random r = new Random(9);
        for (int i = 0; i < 2000; i++) {
            String key = key(r);
            Object v = keyValue(key, r);
            check(v instanceof Map || v instanceof String || v instanceof Bin, "a key's value " + v);
            if (v instanceof Bin && ((Bin) v).length() > 0) {
                byte first = ((Bin) v).bytes()[0];
                check(first != 'b' && (first != (byte) 0x82
                        || Arrays.asList(NOT_OBJECTS).contains(v)), "a byte[] " + v);
            }
        }
    }

    // ======== The run against BergDB ========

    /**
     * A short retain duration, a second (the least a database takes), in clock units; the
     * clock moves up to STEP_UNITS before each operation, so reclaim cuts old lookup times.
     */
    static final long RETAIN_UNITS = bergdb.pub.util.Clock.UNITS_PER_SEC;
    static final int STEP_UNITS = (int) (RETAIN_UNITS / 5);

    final long seed;
    final IndexReference ref;
    final boolean restarts;
    final int threads;
    final Model m = new Model();
    final Generator gen;
    final TestClock clock = new TestClock();
    final StringBuilder trace = new StringBuilder();
    final Random checks;
    MemoryStream stream;
    String dir;
    Database db;
    Connection c;
    int step;
    
    /** What the run checked: active indexes, scans, scan results, raw entries compared. */
    final long[] counts = new long[4];
    
    /** The counts of the last run of run(), for the tests. */
    static long[] lastCounts = new long[4];

    IndexHarness(long seed, Fault fault, boolean restarts, int threads) {
        this.seed = seed;
        this.ref = new IndexReference(fault);
        this.restarts = restarts;
        this.threads = threads;
        this.gen = new Generator(seed);
        this.checks = new Random(seed * 1000003 + 17);
    }

    /**
     * Runs steps operations of seed; fails with the seed, the step and the last operations.
     * dir null: a MemoryStream. threads > 1: the transactions in that many writer threads at
     * once. restartEvery > 0: a restart every that many operations as well as the random ones.
     */
    static void run(long seed, int steps, Fault fault, File dir, int threads, int restartEvery) {
        IndexHarness h = new IndexHarness(seed, fault, true, threads);
        h.dir = dir == null ? null : dir.getPath();
        try {
            h.start(new MemoryStream());
            for (h.step = 0; h.step < steps; h.step++) {
                if (restartEvery > 0 && h.step > 0 && h.step % restartEvery == 0) {
                    h.restart();
                }
                h.step();
            }
        } catch (Throwable e) {
            AssertionError a = new AssertionError("IndexHarness, seed " + seed + ", fault "
                    + fault + ", step " + h.step + ": " + e + "\nThe last operations:\n"
                    + h.lastTrace());
            a.initCause(e);
            throw a;
        } finally {
            lastCounts = h.counts.clone();
            if (h.db != null) {
                h.db.close();
            }
        }
    }

    private void log(String s) {
        trace.append(step).append(": ").append(s).append('\n');
        if (trace.length() > 1000000) {
            trace.delete(0, 100000);
        }
    }

    private String lastTrace() {
        String s = trace.toString();
        int from = s.length();
        for (int i = 0; i < 30 && from > 0; i++) {
            from = s.lastIndexOf('\n', from - 2) + 1;
        }
        return s.substring(from);
    }

    private void start(MemoryStream ms) {
        stream = ms;
        DatabaseBuilder b;
        if (dir == null) {
            b = ((DatabaseBuilderImp) Factory.database()).mainStream(ms);
        } else if (ms == null) {
            b = Factory.database().open(dir);
        } else {
            b = Factory.database().create(dir);
        }
        db = b.clock(clock).start();
        db.setRetainDuration(Duration.units(RETAIN_UNITS));
        c = db.connection();
    }

    private void restart() {
        log("restart");
        db.close();
        db = null;
        start(dir == null ? stream.copy() : null);
    }

    /** The database's current time: after every transaction committed, before every later one. */
    private long now() {
        return db.currentTime().units();
    }

    private void step() {
        clock.setTime(Time.units(clock.getTime() + checks.nextInt(STEP_UNITS)));
        Op op = gen.op(m, restarts);
        log(op.toString());
        if (op instanceof Tx) {
            if (threads > 1) {
                txs((Tx) op);
            } else {
                Tx tx = (Tx) op;
                m.commit(execute(c, tx), tx.writes);
            }
        } else if (op instanceof Create) {
            create((Create) op);
        } else if (op instanceof DeleteIndex) {
            deleteIndex(((DeleteIndex) op).name);
        } else if (op instanceof Join) {
            join(((Join) op).name);
        } else {
            restart();
        }

        // After each operation, at the latest time and at 5 random past lookup times
        // (bergdb 020-10, section 9.1).
        long t = now();
        checkAt(t, true);
        {
            long first = db.getFirstAvailableLookupTime().units();
            List<Long> past = new ArrayList<Long>(m.times.tailSet(first));
            for (int i = 0; i < 5 && !past.isEmpty(); i++) {
                checkAt(past.get(checks.nextInt(past.size())), false);
            }
        }
    }

    /** Executes tx on the connection; returns its time. */
    private static long execute(Connection c, final Tx tx) {
        Transaction t;
        if (tx.rw) {
            t = c.rw(env -> {
                for (Write w : tx.writes) {
                    if (w.value == null) {
                        env.delete(w.key);
                    } else {
                        env.put(w.key, javaValue(w.value));
                    }
                }
            });
        } else {
            WBuilder b = c.w();
            for (Write w : tx.writes) {
                if (w.value == null) {
                    b.delete(w.key);
                } else {
                    b.put(w.key, javaValue(w.value));
                }
            }
            t = b.execute();
        }
        return t.getTime().units();
    }

    /** tx and threads - 1 more transactions, each in its own thread and connection, at once. */
    private void txs(Tx first) {
        final List<Tx> txs = new ArrayList<Tx>();
        txs.add(first);
        for (int i = 1; i < threads; i++) {
            txs.add(gen.tx());
            log(txs.get(i).toString());
        }
        final long[] times = new long[txs.size()];
        final Throwable[] failed = new Throwable[1];
        List<Thread> ts = new ArrayList<Thread>();
        for (int i = 0; i < txs.size(); i++) {
            final int k = i;
            final Connection ck = k == 0 ? c : db.newConnection();
            Thread th = new Thread(() -> {
                try {
                    times[k] = execute(ck, txs.get(k));
                } catch (Throwable e) {
                    failed[0] = e;
                }
            });
            ts.add(th);
            th.start();
        }
        for (Thread th : ts) {
            try {
                th.join();
            } catch (InterruptedException e) {
                throw new AssertionError(e);
            }
        }
        if (failed[0] != null) {
            throw new AssertionError("a writer thread: " + failed[0], failed[0]);
        }
        for (int i = 0; i < txs.size(); i++) {
            m.commit(times[i], txs.get(i).writes);
        }
    }

    private void create(Create op) {
        Def def = op.def;
        boolean used = m.live(def.name) != null;
        long before = now();
        Job job;
        try {
            IndexBuilder b = db.indexBuilder(def.name).dir(def.dir);
            for (Level l : def.levels) {
                b.type(l.type.string);
                switch (l.call) {
                case FIELD:
                    b.field(l.path[0]);
                    break;
                case NESTED_STRING:
                    b.nestedField(String.join(".", l.path));
                    break;
                default:
                    b.nestedField(l.path.clone());
                }
            }
            job = b.start();
        } catch (IndexAlreadyExistsException e) {
            check(used, "IndexAlreadyExistsException for a free name: " + e);
            return;
        }
        check(!used, "a creation of a used name did not throw");
        Generation g = m.create(def, before, now());
        g.g = ((DatabaseImp) db).getIndexManager().definition(def.name).gen();
        if (op.join) {
            JobStatus s = job.join();
            check(s.state() == JobStatus.State.ACTIVE, "start().join(): " + s.note());
            g.activated.doneAt(now());
        }
    }

    private void deleteIndex(String name) {
        Generation g = m.live(name);
        long before = now();
        try {
            db.deleteIndex(name);
        } catch (NoSuchIndexException e) {
            check(g == null, "NoSuchIndexException for an index in use: " + e);
            return;
        }
        check(g != null, "deleteIndex of a free name did not throw");
        g.deleted.set(before, now());
    }

    private void join(String name) {
        Generation g = m.live(name);
        JobStatus s = db.indexJob(name).join();
        check(s.state() == JobStatus.State.ACTIVE, "join of " + name + ": " + s.note());
        g.activated.doneAt(now());
    }

    /**
     * The checks at the lookup time t: for each index name, useIndex at t throws
     * NoSuchIndexException unless the model's index is active at t (a state the model does
     * not know yet is learnt); for an active one, every scan of queries() gives the
     * reference's kvs(), key by key and value by value; and the index's raw entries at t
     * are the reference's (all of them for an active index, some for a building one).
     */
    private void checkAt(long t, boolean latest) {
        Connection rc = db.newConnection();
        rc.setLookupTime(Time.units(t));
        for (String name : INDEX_NAMES) {
            List<Generation> gs = m.at(name, t);
            check(gs.size() <= 1, "two generations of " + name + " at " + t + ": " + gs);
            Generation g = gs.isEmpty() ? null : gs.get(0);
            State state = g == null ? State.ABSENT : g.stateAt(t);
            boolean active;
            try {
                rc.useIndex(name, DbObject.class);
                active = true;
            } catch (NoSuchIndexException e) {
                active = false;
            } catch (LookupTimeNotAvailableException e) {
                check(!latest, "the latest time not available");
                return;
            }
            if (active) {
                counts[0]++;
                check(state == State.ACTIVE || state == State.UNKNOWN,
                        "useIndex(" + name + ") at " + t + " works, the model: " + state);
                g.activated.doneAt(t);
                checkScans(rc, g, t);
            } else {
                check(state != State.ACTIVE, "useIndex(" + name + ") at " + t
                        + ": NoSuchIndexException, the model: active, " + g);
                if (g != null && g.created.at(t) > 0 && g.deleted.at(t) < 0) {
                    g.activated.notDoneAt(t);
                }
            }
            if (g != null && g.g >= 0) {
                checkRawEntries(g, t, g.stateAt(t));
            }
        }
    }

    private void checkScans(Connection rc, Generation g, long t) {
        Def def = g.def;
        List<Entry> entries = ref.entries(def, m.dirAt(def.dir, t));
        for (Query q : queries(def, entries, checks)) {
            List<Entry> expected = ref.filter(def, entries, q);
            List<Kv<DbObject>> got = new ArrayList<Kv<DbObject>>();
            try {
                for (Kv<DbObject> kv : use(rc, def, q).kvs()) {
                    got.add(kv);
                }
            } catch (LookupTimeNotAvailableException e) {
                return;
            }
            counts[1]++;
            counts[2] += got.size();
            int n = Math.min(got.size(), expected.size());
            for (int i = 0; i < n; i++) {
                Entry e = expected.get(i);
                Kv<DbObject> kv = got.get(i);
                check(e.key.equals(kv.key()), "scan " + q + " of " + def + " at " + t
                        + ", result " + i + ": " + IndexReference.show(kv.key()) + ", not "
                        + e + "; all: " + expected);
                check(Arrays.equals(toDbObject(e.value).getBytes(), kv.value().getBytes()),
                        "scan " + q + " of " + def + " at " + t + ", the value at " + e.key);
            }
            check(got.size() == expected.size(), "scan " + q + " of " + def + " at " + t
                    + ": " + got.size() + " results, not " + expected.size() + ": " + expected);
        }
    }

    /** The builder of q on the index. */
    private static UseIndexBuilder<DbObject> use(Connection rc, Def def, Query q) {
        UseIndexBuilder<DbObject> b = rc.useIndex(def.name, DbObject.class);
        for (Object v : q.eq) {
            if (v instanceof Long) {
                b.eq((Long) v);
            } else if (v instanceof Double) {
                b.eq((Double) v);
            } else if (v instanceof String) {
                b.eq((String) v);
            } else {
                b.eq(((Bin) v).bytes());
            }
        }
        if (q.from != null) {
            if (q.from instanceof Long) {
                b.from((Long) q.from, q.fromInclusive);
            } else if (q.from instanceof Double) {
                b.from((Double) q.from, q.fromInclusive);
            } else if (q.from instanceof String) {
                b.from((String) q.from, q.fromInclusive);
            } else {
                b.from(((Bin) q.from).bytes(), q.fromInclusive);
            }
        }
        if (q.to != null) {
            if (q.to instanceof Long) {
                b.to((Long) q.to, q.toInclusive);
            } else if (q.to instanceof Double) {
                b.to((Double) q.to, q.toInclusive);
            } else if (q.to instanceof String) {
                b.to((String) q.to, q.toInclusive);
            } else {
                b.to(((Bin) q.to).bytes(), q.toInclusive);
            }
        }
        if (q.prefix instanceof String) {
            b.prefix((String) q.prefix);
        } else if (q.prefix instanceof Bin) {
            b.prefix(((Bin) q.prefix).bytes());
        }
        if (q.backward) {
            b.backward();
        }
        return b;
    }

    /**
     * The raw entries of g's generation at t equal f over the model (bergdb 020-10, section
     * 9.1): all of them for an active index, some of them for a building one; so a stale
     * entry that a scan's check hides still fails.
     */
    private void checkRawEntries(Generation g, long t, State state) {
        if (state != State.ACTIVE && state != State.BUILDING) {
            return;
        }
        List<Entry> raw;
        try {
            raw = rawEntries(g, t);
        } catch (LookupTimeNotAvailableException e) {
            return;
        }
        List<Entry> expected = ref.expectedEntries(m, g, t);
        counts[3] += raw.size();
        if (state == State.ACTIVE) {
            check(raw.equals(expected), "the raw entries of " + g.def + " at " + t + ": " + raw
                    + ", not " + expected);
        } else {
            check(expected.containsAll(raw), "a raw entry of the building " + g.def + " at " + t
                    + " is not f of a value: " + raw + ", f: " + expected);
        }
    }

    /**
     * The generation's entries at t (IndexManager.entries(), for tests), each parsed by
     * IndexKeys into the reference's Entry: its levels' values, its key (020-10, section 4).
     */
    private List<Entry> rawEntries(Generation g, long t) {
        Def def = g.def;
        char[] types = new char[def.levels.size()];
        for (int i = 0; i < types.length; i++) {
            types[i] = IndexKeys.type(def.type(i).string);
        }
        byte[] prefix = IndexKeys.generationPrefix(def.name, g.g);
        List<Entry> result = new ArrayList<Entry>();
        for (byte[] key : ((DatabaseImp) db).getIndexManager().entries(def.name, g.g, t)) {
            IndexKeys.Entry e = IndexKeys.parseEntry(key, prefix, types);
            List<Object> levels = new ArrayList<Object>();
            for (int i = 0; i < types.length; i++) {
                Object v = e.value(i);
                levels.add(v instanceof byte[] ? new Bin((byte[]) v) : v);
            }
            result.add(new Entry(levels, def.dir + e.fileName().substring(1), null));
        }
        return result;
    }

    /** The model's value as the value to put: an object as a DbObject, a String, a byte[]. */
    static Object javaValue(Object v) {
        if (v instanceof Map) {
            return toDbObject(v);
        } else if (v instanceof Bin) {
            return ((Bin) v).bytes();
        }
        return v;
    }

    static DbObject toDbObject(Object v) {
        DbObject.Builder b = new DbObject.Builder();
        for (Map.Entry<?, ?> e : ((Map<?, ?>) v).entrySet()) {
            b.addDbValue((String) e.getKey(), dbValue(e.getValue()));
        }
        return b.build();
    }

    private static DbValue dbValue(Object v) {
        if (v instanceof Long) {
            return new DbLong((Long) v);
        } else if (v instanceof Double) {
            return new DbDouble((Double) v);
        } else if (v instanceof String) {
            return new DbString((String) v);
        } else if (v instanceof Bin) {
            return new DbByteArray(((Bin) v).bytes());
        } else if (v instanceof Boolean) {
            return new DbBoolean((Boolean) v);
        } else if (v instanceof List) {
            DbArray.Builder a = new DbArray.Builder();
            for (Object x : (List<?>) v) {
                a.add(dbValue(x));
            }
            return a.build();
        }
        return toDbObject(v);
    }

    // ======== Tests against BergDB ========

    /** The unit size (bergdb 020-10, section 9.1): 4 seeds of 400 operations, at most 3 s. */
    @Nano
    public static void testSeeds() {
        long[] all = new long[4];
        for (long seed = 1; seed <= 4; seed++) {
            run(seed, 400, Fault.NONE, null, 1, 0);
            for (int i = 0; i < 4; i++) {
                all[i] += lastCounts[i];
            }
        }
        check(all[0] > 500 && all[1] > 2000 && all[2] > 2000 && all[3] > 2000,
                "the run checked too little: active " + all[0] + ", scans " + all[1]
                + ", results " + all[2] + ", raw entries " + all[3]);
    }

    /** A short run in a directory, with restarts, through the Pub API's create() and open(). */
    @Nano
    public static void testSeedDirectory(TestEnvironment c) throws IOException {
        run(5, 200, Fault.NONE, new File(c.createTempDir(), "db"), 1, 50);
    }

    /** Its own check: each planted fault is found, on one of the unit's seeds. */
    @Nano
    public static void testPlantedFaultsFound() {
        for (Fault f : FAULTS) {
            boolean found = false;
            for (long seed = 1; seed <= 4 && !found; seed++) {
                try {
                    run(seed, 400, f, null, 1, 0);
                } catch (AssertionError e) {
                    found = true;
                }
            }
            check(found, "the planted fault " + f + " was not found");
        }
    }

    /**
     * The night's size: 40 seeds of 5,000 operations, a restart every 500, 4 writer
     * threads; one seed in four in a directory. New seeds each day, printed.
     */
    @Nano("night")
    public static void testSeedsLong(TestEnvironment c) throws IOException {
        long base = System.currentTimeMillis() / 86400000L * 1000;
        c.out().println("IndexHarness: seeds " + base + " to " + (base + 39)
                + ", 5000 operations each");
        for (long seed = base; seed < base + 40; seed++) {
            run(seed, 5000, Fault.NONE,
                    seed % 4 == 0 ? new File(c.createTempDir(), "db" + seed) : null, 4, 500);
        }
    }

    /** Usage: IndexHarness [SEED [STEPS [THREADS]]]: repeats one seed. */
    public static void main(String[] args) {
        long seed = args.length > 0 ? Long.parseLong(args[0]) : System.nanoTime();
        int steps = args.length > 1 ? Integer.parseInt(args[1]) : 5000;
        int threads = args.length > 2 ? Integer.parseInt(args[2]) : 1;
        System.out.println("IndexHarness: seed " + seed + ", " + steps + " operations, "
                + threads + " threads");
        run(seed, steps, Fault.NONE, null, threads, 500);
        System.out.println("IndexHarness OK: active indexes checked " + lastCounts[0]
                + ", scans " + lastCounts[1] + ", scan results " + lastCounts[2]
                + ", raw entries compared " + lastCounts[3]);
    }
}
