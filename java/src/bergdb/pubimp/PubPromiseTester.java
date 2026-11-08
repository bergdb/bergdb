package bergdb.pubimp;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.TreeMap;

import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.Action;
import bergdb.pub.Connection;
import bergdb.pub.DataFormatException;
import bergdb.pub.Database;
import bergdb.pub.DatabaseBuilder;
import bergdb.pub.Factory;
import bergdb.pub.Kv;
import bergdb.pub.RwEnvironment;
import bergdb.pub.TestClock;
import bergdb.pub.Time;
import bergdb.pub.Transaction;
import bergdb.pub.TransactionInfo;
import bergdb.pub.WBuilder;
import bergdb.stream.MemoryStream;

/**
 * Harness 6.7 of release 2026.3, the Pub API's promises (bergdb 018-01, section 6.7;
 * bergdb 018-04). Random sequences of the Pub API's calls on String and byte[] values, run
 * against BergDB and against a simple reference: a map of each key's versions by time. Every
 * answer must be the reference's, as the Javadoc promises it. DbObject and user indexes are
 * experimental (bergdb 018-01, D2) and left out.
 *
 * <p>Each run has a seed, printed at a failure, so that it can be repeated:
 * {@code run(seed, steps)}.</p>
 *
 * @author Frans Lundberg
 */
public class PubPromiseTester {

    /**
     * The known faults that the reference models as the code behaves, not as the Javadoc
     * says, so that the harness passes on main until they are fixed; one line each. A fix
     * makes the harness fail until its line is removed: the reference then expects the
     * fault. With -Dbergdb.promise.skip=none, nothing is skipped.
     */
    static final String[] SKIP = {
    };

    static boolean skips(String entry) {
        if ("none".equals(System.getProperty("bergdb.promise.skip"))) {
            return false;
        }
        return Arrays.asList(SKIP).contains(entry);
    }

    /** The keys: without a suffix, .txt and .bin (Object.class reads them differently). */
    static final String[] KEYS = {"/a", "/b", "/c", "/d/e", "/d/f", "/t.txt", "/u.txt",
            "/v.bin", "/w.bin", "/\u00e5/\u20ac\ud83d\ude00.txt"};

    /** Keys with ${transactionTime}, for key replace (Connection.setEnableKeyReplace()). */
    static final String[] REPLACE_KEYS = {"/r/${transactionTime}", "/r/${transactionTime}.txt",
            "/r/x${transactionTime}y${transactionTime}.bin"};

    /** Invalid keys: every call that takes a key throws IllegalArgumentException. */
    static final String[] INVALID_KEYS = {null, "", "a", "/", "/a/", "/a\ud800b", "/d/"};

    // ======== The reference ========

    /** A user's KV of a transaction: value null for a delete. */
    static final class RefKv {
        final String key;
        final byte[] value;
        /** A delete of a key that had no entry: left out of kvs() (bergdb 018-04, Q4). */
        boolean ofMissing;

        RefKv(String key, byte[] value) {
            this.key = key;
            this.value = value;
        }

        public String toString() {
            return key + "=" + (value == null ? "(delete)" : show(value));
        }
    }

    /** The reference database: each key's versions by time, and each transaction's KVs. */
    static final class Ref {
        final TreeMap<String, TreeMap<Long, byte[]>> versions =
                new TreeMap<String, TreeMap<Long, byte[]>>();
        final TreeMap<Long, List<RefKv>> transactions = new TreeMap<Long, List<RefKv>>();
        /**
         * The time of the last transaction seen, of any kind; before the harness's first,
         * that of the database's own, which a new database writes (set at the first start).
         */
        long lastTime = -1;

        void commit(long time, List<RefKv> kvs, boolean replace) {
            if (time <= lastTime) {
                throw new AssertionError("transaction time " + time + " not after the last, "
                        + lastTime);
            }
            lastTime = time;
            // The last operation on a key in a transaction is the one kept.
            // The last call on a key wins, a key as written; then ${transactionTime} is
            // replaced in a put's key; a delete's key is taken as written (bergdb 019-15).
            TreeMap<String, RefKv> last = new TreeMap<String, RefKv>();
            for (RefKv kv : kvs) {
                last.put(kv.key, kv);
            }
            TreeMap<String, RefKv> made = new TreeMap<String, RefKv>();
            for (RefKv kv : last.values()) {
                boolean r = replace && kv.value != null;
                RefKv k = r ? new RefKv(replaced(kv.key, time), kv.value) : kv;
                made.put(k.key, k);
            }
            List<RefKv> list = new ArrayList<RefKv>(made.values());
            transactions.put(time, list);
            for (RefKv kv : list) {
                kv.ofMissing = kv.value == null && value(kv.key, time) == null;
                TreeMap<Long, byte[]> v = versions.get(kv.key);
                if (v == null) {
                    v = new TreeMap<Long, byte[]>();
                    versions.put(kv.key, v);
                }
                v.put(time, kv.value);
            }
        }

        /**
         * The key with every ${transactionTime} replaced by the time, 18 digits, as
         * RwEnvironmentImp does (the Javadoc does not give the form).
         */
        static String replaced(String key, long time) {
            return key.replace("${transactionTime}", String.format("%018d", time));
        }

        /** The value of key at time, null if none. */
        byte[] value(String key, long time) {
            Map.Entry<Long, byte[]> e = entry(key, time);
            return e == null ? null : e.getValue();
        }

        /** The version of key at time, null if none; its value null for a delete. */
        Map.Entry<Long, byte[]> entry(String key, long time) {
            TreeMap<Long, byte[]> v = versions.get(key);
            return v == null ? null : v.floorEntry(time);
        }
    }

    /** No time. */
    static final long NONE = Long.MIN_VALUE;

    /** The reference state of a connection. */
    static final class RefConn {
        Connection c;
        long requested = Time.MAX.units();
        boolean frozen;
        /** The frozen time, NONE until the first read after freezeLookupTime(). */
        long frozenAt = NONE;
        /** The time of the transaction that wrote the last value found, -1 if none. */
        long infoTime = -1;
        /** Key replace enabled. */
        boolean keyReplace;

        void setLookupTime(long t) {
            requested = t;
            frozen = false;
            frozenAt = NONE;
        }

        /**
         * freezeLookupTime(): the lookup time Time.MAX, frozen at the next read; each call
         * freezes anew, also after setLookupTime() (bergdb 018-04, Q2).
         */
        void freeze() {
            requested = Time.MAX.units();
            frozen = true;
            frozenAt = NONE;
        }

        /**
         * getLookupTime(): the requested time, or after freezeLookupTime() and a read, the
         * frozen time (bergdb 018-04, Q3).
         */
        long lookupTime() {
            return frozen && frozenAt != NONE ? frozenAt : requested;
        }

        /** The time a read reads at, freezing it if frozen. */
        long readTime(Ref ref) {
            long t = Math.min(requested, ref.lastTime);
            if (frozen) {
                if (frozenAt == NONE) {
                    frozenAt = t;
                }
                return frozenAt;
            }
            return t;
        }
    }

    // ======== The run ========

    final long seed;
    final Random random;
    final Ref ref = new Ref();
    final TestClock clock = new TestClock();
    final RefConn[] conns = {new RefConn(), new RefConn()};
    final StringBuilder trace = new StringBuilder();
    MemoryStream stream;
    /** The database's directory, or null for a MemoryStream. */
    String dir;
    /**
     * Small mode, the seeds that are 2 modulo 4: the smallest startup distance (5 MB) and
     * cache (4 MB), 300 more keys, and values of up to 60 KB, so that a run of 10,000 steps
     * writes some 30 MB, and eviction drops nodes and values that reads then load again.
     */
    final boolean small;
    Database db;
    int step;
    /** Keys made by writes with ${transactionTime}, replaced or not, for reads. */
    final List<String> madeKeys = new ArrayList<String>();
    /** The last currentTime() returned. */
    long lastCurrentTime = NONE;

    PubPromiseTester(long seed) {
        this.seed = seed;
        this.random = new Random(seed);
        this.small = seed % 4 == 2;
    }

    /** Runs a sequence of steps calls on one seed; fails with the seed and the last calls. */
    public static void run(long seed, int steps) {
        run(seed, steps, null);
    }

    /**
     * Runs a sequence of steps calls on one seed, in a database in the directory dir, which
     * must not hold one, or, if dir is null, on a MemoryStream; fails with the seed and the
     * last calls.
     */
    public static void run(long seed, int steps, File dir) {
        PubPromiseTester t = new PubPromiseTester(seed);
        t.dir = dir == null ? null : dir.getPath();
        try {
            t.start(new MemoryStream());
            for (t.step = 0; t.step < steps; t.step++) {
                t.step();
            }
            if (Boolean.getBoolean("bergdb.promise.verbose")) {
                System.out.println("seed " + seed + (t.small ? ", small" : "") + ": "
                        + ((DatabaseImp) t.db).getDb().internal().eviction().summary());
            }
        } catch (Throwable e) {
            AssertionError a = new AssertionError("PubPromiseTester, seed " + seed + ", step "
                    + t.step + ": " + e + "\nThe last calls:\n" + t.lastTrace());
            a.initCause(e);
            throw a;
        } finally {
            if (t.db != null) {
                t.db.close();
            }
        }
    }

    private String lastTrace() {
        String s = trace.toString();
        int from = s.length();
        int lines = Integer.getInteger("bergdb.promise.lines", 30);
        for (int i = 0; i < lines && from > 0; i++) {
            from = s.lastIndexOf('\n', from - 2) + 1;
        }
        return s.substring(from);
    }

    private void log(String s) {
        trace.append(step).append(": ").append(s).append('\n');
        if (trace.length() > 2000000) {
            trace.delete(0, 100000);
        }
    }

    /**
     * Starts the database: on the MemoryStream m, or, with a directory, by the Pub API's
     * create() the first time and open() at a restart.
     */
    private void start(MemoryStream m) {
        stream = m;
        DatabaseBuilder b;
        if (dir == null) {
            b = ((DatabaseBuilderImp) Factory.database()).mainStream(m);
        } else if (m == null) {
            b = Factory.database().open(dir);
        } else {
            b = Factory.database().create(dir);
        }
        if (small) {
            b.startupDistanceInMb(5).cacheSizeInMb(4);
        }
        db = b.clock(clock).start();
        if (ref.lastTime == -1) {
            // The time of the new database's own transaction, which a read before the
            // harness's first transaction reads at, and freezes (getLookupTime(), bergdb
            // 018-04, Q3). The clock is at 0, before that time, so currentTime() returns it.
            ref.lastTime = db.currentTime().units();
        }
        conns[0] = new RefConn();
        conns[0].c = db.connection();
        conns[1] = new RefConn();
        conns[1].c = db.newConnection();
        check("connection()'s lookup time", Time.MAX, conns[0].c.getLookupTime());
        check("newConnection()'s lookup time", Time.MAX, conns[1].c.getLookupTime());
    }

    private void restart() {
        log("restart");
        db.close();
        db = null;
        // currentTime()'s promise, "less than the transaction time of any future
        // transaction", is for this started database (its Javadoc): a restart forgets the
        // times it returned, and with a clock that has not moved, the next transaction can
        // have one of them (bergdb 018-04, Q5).
        lastCurrentTime = NONE;
        start(dir == null ? stream.copy() : null);
    }

    private void step() {
        if (random.nextInt(4) == 0) {
            clock.setTime(Time.units(clock.getTime() + random.nextInt(1000)));
        }
        RefConn rc = conns[random.nextInt(2)];
        int r = random.nextInt(100);
        if (r < 14) {
            put(rc);
        } else if (r < 20) {
            delete(rc);
        } else if (r < 32) {
            w(rc);
        } else if (r < 42) {
            if (random.nextInt(20) == 0) {
                rwRerun(rc);
            } else {
                rw(rc);
            }
        } else if (r < 62) {
            get(rc);
        } else if (r < 70) {
            exists(rc);
        } else if (r < 78) {
            transactionInfo(rc);
        } else if (r < 86) {
            setLookupTime(rc);
        } else if (r < 92) {
            freeze(rc);
        } else if (r < 95) {
            currentTime(rc);
        } else if (r < 96) {
            connectionAgain();
        } else if (r < 97) {
            if (random.nextBoolean()) {
                keyReplace(rc);
            } else {
                invalid(rc);
            }
        } else if (r < 98) {
            // Small mode restarts one time in 20 as often, so that a run passes its startup
            // distance and eviction has nodes to drop.
            if (!small || random.nextInt(20) == 0) {
                restart();
            }
        } else {
            getLookupTime(rc);
        }
    }

    /** A key to read: one of KEYS, or now and then one that a write with key replace made. */
    private String key() {
        if (random.nextInt(8) == 0 && !madeKeys.isEmpty()) {
            return madeKeys.get(random.nextInt(madeKeys.size()));
        }
        if (small && random.nextBoolean()) {
            return "/k/" + random.nextInt(300) + (random.nextBoolean() ? ".bin" : "");
        }
        return KEYS[random.nextInt(KEYS.length)];
    }

    /** A key to write: now and then one with ${transactionTime}. */
    private String writeKey() {
        if (random.nextInt(12) == 0) {
            return REPLACE_KEYS[random.nextInt(REPLACE_KEYS.length)];
        }
        return key();
    }

    /** A String or byte[] value, random; bytes never start with DbObject's header. */
    private Object value() {
        int n = random.nextInt(4) == 0 ? random.nextInt(small ? 60000 : 3000)
                : random.nextInt(12);
        if (random.nextBoolean()) {
            StringBuilder sb = new StringBuilder();
            for (int i = 0; i < n; i++) {
                int k = random.nextInt(10);
                sb.append(k < 7 ? (char) ('a' + random.nextInt(26)) : k < 9 ? 'å' : '€');
            }
            return sb.toString();
        } else {
            byte[] b = new byte[n];
            random.nextBytes(b);
            if (n > 0 && b[0] == DbObject.HEADER) {
                b[0] = 0;
            }
            return b;
        }
    }

    private static byte[] bytes(Object value) {
        return value instanceof String ? Utf8.bytes((String) value) : ((byte[]) value).clone();
    }

    private static String show(Object value) {
        if (value == null) {
            return "null";
        }
        if (value instanceof byte[]) {
            byte[] b = (byte[]) value;
            String s = Arrays.toString(b.length > 8 ? Arrays.copyOf(b, 8) : b);
            return b.length > 8 ? s.substring(0, s.length() - 1) + ", ...] (" + b.length
                    + " bytes, hash " + Arrays.hashCode(b) + ")" : s;
        }
        String s = "'" + value + "'";
        return s.length() > 40 ? s.substring(0, 40) + "...' (" + s.length() + " chars, hash "
                + s.hashCode() + ")" : s;
    }

    /** Changes the caller's array after a put: the stored value must not change (015-47). */
    private static void scribble(Object value) {
        if (value instanceof byte[]) {
            Arrays.fill((byte[]) value, (byte) 'x');
        }
    }

    private int ci(RefConn rc) {
        return rc == conns[0] ? 0 : 1;
    }

    // ======== The calls ========

    private void put(RefConn rc) {
        String key = writeKey();
        Object value = value();
        byte[] b = bytes(value);
        log("c" + ci(rc) + ".put(" + key + ", " + show(value) + ")");
        Transaction t = rc.c.put(key, value);
        scribble(value);
        commit(t, Arrays.asList(new RefKv(key, b)), rc.keyReplace);
    }

    private void delete(RefConn rc) {
        String key = writeKey();
        log("c" + ci(rc) + ".delete(" + key + ")");
        Transaction t = rc.c.delete(key);
        commit(t, Arrays.asList(new RefKv(key, null)), rc.keyReplace);
    }

    private void w(RefConn rc) {
        WBuilder wb = rc.c.w();
        List<RefKv> kvs = new ArrayList<RefKv>();
        List<Object> values = new ArrayList<Object>();
        StringBuilder s = new StringBuilder("c" + ci(rc) + ".w()");
        int n = 1 + random.nextInt(5);
        for (int i = 0; i < n; i++) {
            String key = writeKey();
            if (random.nextInt(4) == 0) {
                s.append(".delete(" + key + ")");
                wb.delete(key);
                kvs.add(new RefKv(key, null));
            } else {
                Object value = value();
                s.append(".put(" + key + ", " + show(value) + ")");
                kvs.add(new RefKv(key, bytes(value)));
                wb.put(key, value);
                values.add(value);
            }
        }
        log(s + ".execute()");
        for (Object value : values) {
            scribble(value);
        }
        Transaction t = wb.execute();
        for (Object value : values) {
            scribble(value);
        }
        commit(t, kvs, rc.keyReplace);
    }

    private void commit(Transaction t, List<RefKv> kvs, boolean replace) {
        long time = t.getTime().units();
        commit(time, kvs, replace);
        log("  committed at " + time);
        check("the transaction's output", null, t.getOutput("n", Integer.class));
    }

    /**
     * A transaction at time, in the reference. Its time must be after every currentTime()
     * returned before it: "less than the transaction time of any future transaction".
     */
    private void commit(long time, List<RefKv> kvs, boolean replace) {
        if (time <= lastCurrentTime) {
            throw new AssertionError("transaction time " + time + " not after currentTime() "
                    + lastCurrentTime + ", returned before it");
        }
        ref.commit(time, kvs, replace);
        for (RefKv kv : ref.transactions.get(time)) {
            if (!Arrays.asList(KEYS).contains(kv.key) && !madeKeys.contains(kv.key)
                    && !kv.key.contains("${") && !kv.key.startsWith("/k/")
                    && madeKeys.size() < 200) {
                madeKeys.add(kv.key);
            }
        }
    }

    /**
     * An rw-transaction that conflicts: its first run reads a key, and the other connection
     * then puts the key. The action must run again, as Connection.rw() promises; the second
     * run reads the other's value, and the transaction's output is the second run's.
     */
    private void rwRerun(final RefConn rc) {
        final RefConn other = conns[1 - ci(rc)];
        final String key = key();
        final Object value = value();
        final byte[] b = bytes(value);
        final String key2 = writeKey();
        final Object mine = value();
        final byte[] mb = bytes(mine);
        log("c" + ci(rc) + ".rw(get(" + key + "), then in the first run c" + ci(other)
                + ".put(" + key + ", " + show(value) + "); put(" + key2 + ", " + show(mine)
                + "))");
        final long before = ref.lastTime;
        final int[] runs = {0};
        Transaction t = rc.c.rw(new Action() {
            public void run(RwEnvironment env) {
                runs[0]++;
                byte[] seen = env.get(key, byte[].class);
                if (runs[0] == 1) {
                    checkValue("rw's first run, get(" + key + ")", ref.value(key, before),
                            byte[].class, seen);
                    Transaction o = other.c.put(key, value);
                    long time = o.getTime().units();
                    commit(time, Arrays.asList(new RefKv(key, b)), false);
                    log("  the other's put committed at " + time);
                } else {
                    checkValue("rw's run " + runs[0] + ", get(" + key + ") after the other's "
                            + "put", b, byte[].class, seen);
                }
                env.put(key2, mine);
                env.setOutput("n", runs[0]);
            }
        });
        scribble(mine);
        check("rw's runs, after a conflict", 2, runs[0]);
        long time = t.getTime().units();
        commit(time, Arrays.asList(new RefKv(key2, mb)), rc.keyReplace);
        log("  committed at " + time);
        check("rw's output, the second run's", 2, t.getOutput("n", Integer.class));
    }

    /**
     * An rw-transaction: reads and writes in a random order, the reads now and then of a key
     * that the transaction writes. The reads read one state, the latest as of the first
     * read, and do not see the transaction's own writes (bergdb 018-04, Q1): each is checked
     * against the reference at the latest state.
     */
    private void rw(final RefConn rc) {
        final int writes = random.nextInt(4);
        final List<RefKv> kvs = new ArrayList<RefKv>();
        final List<Object> values = new ArrayList<Object>();
        for (int i = 0; i < writes; i++) {
            String key = writeKey();
            if (random.nextInt(4) == 0) {
                kvs.add(new RefKv(key, null));
                values.add(null);
            } else {
                Object value = value();
                kvs.add(new RefKv(key, bytes(value)));
                values.add(value);
            }
        }
        final int reads = random.nextInt(4);
        final List<String> readKeys = new ArrayList<String>();
        final List<Integer> readKinds = new ArrayList<Integer>();
        for (int i = 0; i < reads; i++) {
            String key = writes > 0 && random.nextInt(3) == 0
                    ? kvs.get(random.nextInt(writes)).key : key();
            readKeys.add(key.contains("${") ? key() : key);
            readKinds.add(random.nextInt(3));
        }
        // The order of the calls: true for a read, false for a write.
        final List<Boolean> order = new ArrayList<Boolean>();
        for (int i = 0; i < reads + writes; i++) {
            order.add(i < reads);
        }
        Collections.shuffle(order, random);
        final int output = random.nextInt(1000);
        StringBuilder o = new StringBuilder();
        for (boolean read : order) {
            o.append(read ? 'r' : 'w');
        }
        log("c" + ci(rc) + ".rw(reads " + readKeys + " kinds " + readKinds + ", writes " + kvs
                + ", order " + o + ", output " + output + ")");
        final long latest = ref.lastTime;
        final int[] runs = {0};
        Transaction t = rc.c.rw(new Action() {
            public void run(RwEnvironment env) {
                runs[0]++;
                int i = 0;
                int w = 0;
                for (boolean read : order) {
                    if (!read) {
                        RefKv kv = kvs.get(w);
                        Object value = values.get(w);
                        w++;
                        if (value == null) {
                            env.delete(kv.key);
                        } else {
                            env.put(kv.key, value);
                        }
                        continue;
                    }
                    String key = readKeys.get(i);
                    byte[] expected = ref.value(key, latest);
                    int kind = readKinds.get(i);
                    if (kind == 0) {
                        checkValue("rw get(" + key + ", String.class)", expected, String.class,
                                asString(() -> env.get(key, String.class)));
                    } else if (kind == 1) {
                        checkValue("rw get(" + key + ", byte[].class)", expected, byte[].class,
                                env.get(key, byte[].class));
                    } else {
                        check("rw exists(" + key + ")", expected != null, env.exists(key));
                    }
                    i++;
                }
                env.setOutput("n", output);
            }
        });
        for (Object value : values) {
            scribble(value);
        }
        check("rw's runs, one connection at a time", 1, runs[0]);
        long time = t.getTime().units();
        commit(time, kvs, rc.keyReplace);
        log("  committed at " + time);
        check("rw's output", output, t.getOutput("n", Integer.class));
    }

    private void get(RefConn rc) {
        String key = key();
        int kind = random.nextInt(3);
        long time = rc.readTime(ref);
        Map.Entry<Long, byte[]> e = ref.entry(key, time);
        byte[] expected = e == null ? null : e.getValue();
        String what = "c" + ci(rc) + ".get(" + key + ", "
                + (kind == 0 ? "String" : kind == 1 ? "byte[]" : "Object") + ".class) at "
                + time;
        log(what);
        if (kind == 0) {
            checkValue(what, expected, String.class, asString(() -> rc.c.get(key, String.class)));
        } else if (kind == 1) {
            checkValue(what, expected, byte[].class, rc.c.get(key, byte[].class));
        } else {
            Object o = asString(() -> rc.c.get(key, Object.class));
            checkValue(what, expected, key.endsWith(".txt") ? String.class : byte[].class, o);
        }
        if (expected != null) {
            rc.infoTime = e.getKey();
        }
    }

    private void exists(RefConn rc) {
        String key = key();
        long time = rc.readTime(ref);
        Map.Entry<Long, byte[]> e = ref.entry(key, time);
        boolean expected = e != null && e.getValue() != null;
        String what = "c" + ci(rc) + ".exists(" + key + ") at " + time;
        log(what);
        check(what, expected, rc.c.exists(key));
        if (expected) {
            rc.infoTime = e.getKey();
        }
    }

    private void transactionInfo(RefConn rc) {
        String what = "c" + ci(rc) + ".transactionInfo(), expected the transaction at "
                + rc.infoTime;
        log(what);
        TransactionInfo info;
        try {
            info = rc.c.transactionInfo();
        } catch (IllegalStateException e) {
            if (rc.infoTime == -1) {
                return;
            }
            throw new AssertionError(what + ": " + e, e);
        }
        if (rc.infoTime == -1) {
            throw new AssertionError(what + ": no value found yet, expected "
                    + "IllegalStateException, got the transaction at " + info.time().units());
        }
        check(what + ", its time", rc.infoTime, info.time().units());
        TreeMap<String, byte[]> actual = new TreeMap<String, byte[]>();
        for (Kv<byte[]> kv : info.kvs()) {
            if (actual.containsKey(kv.key())) {
                throw new AssertionError(what + ": key " + kv.key() + " twice in kvs()");
            }
            actual.put(kv.key(), kv.value());
        }
        // A delete of a key that had no entry is left out (bergdb 018-04, Q4).
        TreeMap<String, byte[]> expected = new TreeMap<String, byte[]>();
        for (RefKv kv : ref.transactions.get(rc.infoTime)) {
            if (!kv.ofMissing) {
                expected.put(kv.key, kv.value);
            }
        }
        check(what + ", its keys (the reference's KVs " + ref.transactions.get(rc.infoTime)
                + ")", expected.keySet().toString(), actual.keySet().toString());
        for (Map.Entry<String, byte[]> kv : expected.entrySet()) {
            byte[] a = actual.get(kv.getKey());
            if (!Arrays.equals(kv.getValue(), a)) {
                throw new AssertionError(what + ", its value of " + kv.getKey() + ": expected "
                        + show(kv.getValue()) + ", got " + show(a));
            }
        }
    }

    private void setLookupTime(RefConn rc) {
        long t;
        int r = random.nextInt(5);
        if (r == 0 || ref.transactions.isEmpty()) {
            t = Time.MAX.units();
        } else {
            Long[] times = ref.transactions.keySet().toArray(new Long[0]);
            t = times[random.nextInt(times.length)];
            if (r == 1) {
                t = Math.max(0, t - 1);
            } else if (r == 2) {
                t = t + 1;
            } else if (r == 3) {
                t = Math.max(0, times[0] - 1 - random.nextInt(3));
            }
        }
        log("c" + ci(rc) + ".setLookupTime(" + t + ")");
        rc.c.setLookupTime(Time.units(t));
        rc.setLookupTime(t);
        check("getLookupTime() after setLookupTime()", Time.units(t), rc.c.getLookupTime());
    }

    /**
     * freezeLookupTime(), also on a frozen connection: each call freezes anew, at the latest
     * state as of the next read, and getLookupTime() is Time.MAX until it (bergdb 018-04,
     * Q2 and Q3).
     */
    private void freeze(RefConn rc) {
        log("c" + ci(rc) + ".freezeLookupTime()" + (rc.frozen ? " again" : ""));
        rc.c.freezeLookupTime();
        rc.freeze();
        check("getLookupTime() after freezeLookupTime()", Time.MAX, rc.c.getLookupTime());
    }

    private void currentTime(RefConn rc) {
        long t = rc.c.currentTime().units();
        log("c" + ci(rc) + ".currentTime() " + t);
        if (t < ref.lastTime) {
            throw new AssertionError("currentTime() " + t + " before the last transaction, "
                    + ref.lastTime);
        }
        long d = db.currentTime().units();
        if (d < t) {
            throw new AssertionError("Database.currentTime() " + d
                    + " before an earlier Connection.currentTime(), " + t);
        }
        lastCurrentTime = d;
        long first = db.getFirstAvailableLookupTime().units();
        if (!ref.transactions.isEmpty() && first > ref.transactions.firstKey()) {
            throw new AssertionError("getFirstAvailableLookupTime() " + first + " after the "
                    + "first transaction, " + ref.transactions.firstKey()
                    + ", with the retain duration forever");
        }
    }

    /** setEnableKeyReplace(): on or off. */
    private void keyReplace(RefConn rc) {
        boolean on = random.nextBoolean();
        log("c" + ci(rc) + ".setEnableKeyReplace(" + on + ")");
        rc.c.setEnableKeyReplace(on);
        rc.keyReplace = on;
        check("getEnableKeyReplace()", on, rc.c.getEnableKeyReplace());
    }

    /**
     * A call with an invalid key, or a null value: IllegalArgumentException, as the Javadoc
     * of each says, and nothing written (the reference is unchanged, and later reads check
     * it). In an rw-transaction the action catches it and goes on.
     */
    private void invalid(final RefConn rc) {
        final String key = INVALID_KEYS[random.nextInt(INVALID_KEYS.length)];
        final int kind = random.nextInt(11);
        final String what = "c" + ci(rc) + ", invalid call " + kind + " with key "
                + (key == null ? "null" : "'" + key + "'");
        log(what);
        final String[] got = {null};
        Runnable call = new Runnable() {
            public void run() {
                switch (kind) {
                case 0: rc.c.put(key, "v"); break;
                case 1: rc.c.delete(key); break;
                case 2: rc.c.get(key, String.class); break;
                case 3: rc.c.get(key, byte[].class); break;
                case 4: rc.c.exists(key); break;
                case 5: rc.c.w().put(key, new byte[] {1}); break;
                case 6: rc.c.w().delete(key); break;
                case 7: rc.c.put(KEYS[0], null); break;
                case 8: rc.c.w().put(KEYS[0], null); break;
                default: break;
                }
            }
        };
        if (kind < 9) {
            got[0] = refusal(call);
        } else {
            Transaction t = rc.c.rw(new Action() {
                public void run(final RwEnvironment env) {
                    final int k = random.nextInt(5);
                    got[0] = "env call " + k + ": " + refusal(new Runnable() {
                        public void run() {
                            switch (k) {
                            case 0: env.put(key, "v"); break;
                            case 1: env.delete(key); break;
                            case 2: env.get(key, String.class); break;
                            case 3: env.exists(key); break;
                            default: env.put(KEYS[0], null); break;
                            }
                        }
                    });
                }
            });
            commit(t, new ArrayList<RefKv>(), false);
        }
        if (got[0] != null && !got[0].endsWith(": null")) {
            throw new AssertionError(what + ": " + got[0]);
        }
    }

    /** Null if call throws IllegalArgumentException, else what it did. */
    private static String refusal(Runnable call) {
        try {
            call.run();
        } catch (IllegalArgumentException e) {
            return null;
        } catch (RuntimeException e) {
            return "expected IllegalArgumentException, got " + e;
        }
        return "expected IllegalArgumentException, it returned";
    }

    /** Database.connection() again: the same object, its requested lookup time Time.MAX. */
    private void connectionAgain() {
        log("db.connection()");
        Connection c = db.connection();
        if (c != conns[0].c) {
            throw new AssertionError("connection() in the same thread gave another object");
        }
        conns[0].setLookupTime(Time.MAX.units());
        check("connection()'s lookup time", Time.MAX, c.getLookupTime());
    }

    /**
     * getLookupTime(): the requested time, or after freezeLookupTime() and a read, the
     * frozen time (bergdb 018-04, Q3).
     */
    private void getLookupTime(RefConn rc) {
        log("c" + ci(rc) + ".getLookupTime()");
        check("getLookupTime()", Time.units(rc.lookupTime()), rc.c.getLookupTime());
    }

    // ======== Checks ========

    private void checkValue(String what, byte[] expected, Class<?> clazz, Object actual) {
        if (expected == null) {
            if (actual != null) {
                throw new AssertionError(what + ": expected no entry, got " + show(actual));
            }
            return;
        }
        if (actual == null) {
            throw new AssertionError(what + ": expected " + show(expected) + ", got null");
        }
        if (clazz == String.class && !Utf8.isWellFormed(expected)) {
            // A reader never repairs ill-formed UTF-8 (bergdb 021-06).
            if (actual != NOT_UTF8) {
                throw new AssertionError(what + ": expected DataFormatException for bytes that "
                        + "are not well-formed UTF-8, " + show(expected) + ", got " + show(actual));
            }
            return;
        }
        if (actual == NOT_UTF8) {
            throw new AssertionError(what + ": DataFormatException, for " + show(expected));
        }
        if (clazz == String.class) {
            if (!(actual instanceof String)) {
                throw new AssertionError(what + ": expected a String, got " + actual.getClass());
            }
            check(what, Utf8.string(expected), actual);
        } else {
            if (!(actual instanceof byte[])) {
                throw new AssertionError(what + ": expected a byte[], got " + actual.getClass());
            }
            if (!Arrays.equals(expected, (byte[]) actual)) {
                throw new AssertionError(what + ": expected " + show(expected) + ", got "
                        + show(actual));
            }
        }
    }

    private static void check(String what, Object expected, Object actual) {
        if (expected == null ? actual != null : !expected.equals(actual)) {
            throw new AssertionError(what + ": expected " + show(expected) + ", got "
                    + show(actual));
        }
    }

    /** UTF-8, as the database converts. */
    /** What asString() gives for a DataFormatException. */
    static final Object NOT_UTF8 = new Object() {
        public String toString() {
            return "DataFormatException";
        }
    };

    /**
     * The value that read gives, or NOT_UTF8 if it throws DataFormatException: a value read
     * as a String that is not well-formed UTF-8 (bergdb 021-06).
     */
    static Object asString(java.util.function.Supplier<Object> read) {
        try {
            return read.get();
        } catch (DataFormatException e) {
            return NOT_UTF8;
        }
    }

    static final class Utf8 {
        static byte[] bytes(String s) {
            return s.getBytes(java.nio.charset.StandardCharsets.UTF_8);
        }

        /** Well-formed UTF-8, by the JDK's decoder set to report. */
        static boolean isWellFormed(byte[] b) {
            try {
                java.nio.charset.StandardCharsets.UTF_8.newDecoder()
                        .onMalformedInput(java.nio.charset.CodingErrorAction.REPORT)
                        .onUnmappableCharacter(java.nio.charset.CodingErrorAction.REPORT)
                        .decode(java.nio.ByteBuffer.wrap(b));
                return true;
            } catch (java.nio.charset.CharacterCodingException e) {
                return false;
            }
        }

        static String string(byte[] b) {
            return new String(b, java.nio.charset.StandardCharsets.UTF_8);
        }
    }

    // ======== Tests ========

    /** Short runs on fixed seeds: the unit tests, about 1 s. */
    @Nano
    public static void testSeeds() {
        for (long seed = 1; seed <= 4; seed++) {
            run(seed, 2000);
        }
    }

    /** A short run in a directory, through the Pub API's create() and open(). */
    @Nano
    public static void testSeedDirectory(TestEnvironment c) throws IOException {
        run(5, 1000, new File(c.createTempDir(), "db"));
    }

    /**
     * Longer runs for the night tests, about a minute: 40 seeds of 10,000 steps, new seeds
     * each day (the day's number times 1000), printed, so that a failure can be repeated with
     * main(seed, 10000); one seed in four (the multiples of 4) in a directory, through
     * FileStream, repeated with main(seed, 10000, 1, DIR).
     */
    @Nano("night")
    public static void testSeedsLong(TestEnvironment c) throws IOException {
        long base = System.currentTimeMillis() / 86400000L * 1000;
        c.out().println("PubPromiseTester: seeds " + base + " to " + (base + 39)
                + ", 10000 steps each");
        for (long seed = base; seed < base + 40; seed++) {
            // One seed in four in a directory, through FileStream.
            run(seed, 10000, seed % 4 == 0 ? new File(c.createTempDir(), "db" + seed) : null);
        }
    }

    /**
     * Usage: PubPromiseTester [SEED [STEPS [RUNS [DIR]]]]. With DIR, each run is in a new
     * directory DIR/dbSEED, which must not exist, as the night's seeds that are multiples of
     * 4 are.
     */
    public static void main(String[] args) {
        long seed = args.length > 0 ? Long.parseLong(args[0]) : System.nanoTime();
        int steps = args.length > 1 ? Integer.parseInt(args[1]) : 20000;
        int runs = args.length > 2 ? Integer.parseInt(args[2]) : 1;
        File parent = args.length > 3 ? new File(args[3]) : null;
        for (int i = 0; i < runs; i++) {
            System.out.println("PubPromiseTester: seed " + (seed + i) + ", " + steps
                    + " steps" + (parent == null ? "" : ", in " + parent));
            run(seed + i, steps, parent == null ? null : new File(parent, "db" + (seed + i)));
        }
        System.out.println("PubPromiseTester OK");
    }
}
