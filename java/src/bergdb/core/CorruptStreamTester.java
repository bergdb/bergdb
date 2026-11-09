package bergdb.core;

import java.io.EOFException;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.TreeMap;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.ThreadFactory;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.function.Supplier;

import bergdb.common.Bytes;
import bergdb.common.StringUtil;
import bergdb.dag.Klong;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.util.DatabaseNotCreatedException;
import bergdb.pub.util.DbException;
import bergdb.pub.util.IllegalDbStateException;
import bergdb.storage.RecoverableStream;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.MemoryStream;

/**
 * Harness 6.1 of release 2026.3, corrupt streams at a start (bergdb 018-01, section 6.1;
 * bergdb 018-07). Streams written by real runs of Db are copied with damage, and each copy is
 * started.
 *
 * <ul>
 * <li><b>Truncation</b>, the crash contract (bergdb 014-01, section 7; AppendOnlyStream's
 * Javadoc), a hard requirement: a copy truncated at any byte starts with exactly the
 * transactions whose records end before the cut, passes the audit, takes one more
 * transaction and starts again with it. A cut in the creation may instead be refused with
 * DatabaseNotCreatedException, with nothing written.</li>
 * <li><b>Other damage</b>, best effort: a byte flipped, a range cut out, a record header's
 * field set (its size, time, startupPos or topPos, a got-dirty entry), a node's field
 * changed with its checksum made right. The start refuses the copy with a DbException, or a
 * read fails the database (P7 of bergdb 010-01), or the copy holds what the original held
 * after some transaction (a damage that does not matter, or that looks like a cut tail).
 * A start or a read that throws anything else, does not end, or leaves the database going on
 * after a failed read, and a copy that answers other values without failing, is a fault,
 * but the damage that Frans decided passes undetected (KNOWN).</li>
 * </ul>
 *
 * <p>The streams are MemoryStream's bytes, and each copy is started on a CopyStream over
 * them, which copies nothing and counts what the start appends.</p>
 *
 * @author Frans Lundberg
 */
public class CorruptStreamTester {

    /**
     * Known faults of this harness's class that are open: their failures are printed and
     * skipped, one entry each, until a fix removes its line. With
     * -Dbergdb.corrupt.skip=none, nothing is skipped.
     */
    static final String[] SKIP = {
    };

    /**
     * Damage that passes undetected by Frans's decision, not a fault (bergdb 018-01, section
     * 6.1): counted, not failed. BergDB assumes correct storage; its checksums and checks of
     * damage other than a cut tail are a best effort (checksums in the stream: bergdb 017-08).
     * <ul>
     * <li>015-73 (2026-11-05, 15:35, option (a)): a record's startupPos set to the start of
     * another record, which the take never reached.</li>
     * <li>014-01 (005-83's case, moved to 014-01): a start that refuses a corrupt record size
     * after recovery's zero fill has written.</li>
     * <li>019-30 (2026-11-06, 10:42, option (a)): a record's time or topPos set, or a byte of
     * them flipped, to a value that passes the start's checks.</li>
     * <li>019-31 (2026-11-06, 10:42, option (a)): a range cut out of the stream's middle,
     * such as whole records: the stream left is a valid stream of fewer transactions.</li>
     * <li>019-33 (2026-11-06, 10:42, option (a)): a node byte flipped by 0xff, between 0x00
     * and 0xff, which Fletcher-16 modulo 255 does not see.</li>
     * </ul>
     */
    static final String[] KNOWN = {"015-73", "014-01", "019-30", "019-31", "019-33"};

    /**
     * The open entry of SKIP that a failure belongs to, or null: a new fault. Each entry
     * says which damage and which failure are its. None since 021-12's fix (2026-11-09).
     */
    static String entryOf(Copy c, String failure) {
        return null;
    }

    static boolean skips(String entry) {
        if ("none".equals(System.getProperty("bergdb.corrupt.skip"))) {
            return false;
        }
        return Arrays.asList(SKIP).contains(entry);
    }

    /** The transaction counter: transaction i puts "/n" = i. */
    static final String COUNTER = "/n";

    /** The keys a workload puts and deletes, besides COUNTER. */
    static final String[] KEYS = {"/a", "/b", "/c", "/d/e", "/d/f", "/d/g/h", "/d/g/i",
            "/k1", "/k2", "/k3", "/k4", "/k5", "/k6", "/x/y/z"};

    /**
     * Keys of three segments (Keys.toSegments), 80 in the last: key nodes that point to key
     * nodes, which KEYS, of one segment, never make (bergdb 021-11).
     */
    static final String[] LONG_KEYS = new String[80];
    static {
        for (int i = 0; i < LONG_KEYS.length; i++) {
            LONG_KEYS[i] = "/longkey/number-" + i;
        }
    }

    /**
     * The most bytes a start and a transaction may append to a copy: recovery of a cut needs
     * at most a record's size. A larger one is recovery's zero fill of a damaged size, which
     * could take 2 GB (014-01, 005-83's case): the append fails.
     */
    static final int MAX_APPENDED = 1 << 20;

    /** The time of transaction i is TIME_STEP * i. */
    static final long TIME_STEP = 10;

    /** The audit (Audit): every AUDIT_EVERY-th transaction and at the start. */
    static final int AUDIT_EVERY = 1000000;

    // ======== The originals ========

    /** A workload that writes an original stream. */
    static final class Config {
        final String name;
        final int startupDistance;
        final int transactions;
        /** Each value is 1 to maxValue bytes; one transaction in bigEvery has a big one. */
        final int maxValue;
        final int bigEvery;
        final int bigValue;
        /** The keys it puts and deletes, besides COUNTER. */
        final String[] keys;

        Config(String name, int startupDistance, int transactions, int maxValue,
                int bigEvery, int bigValue, String[] keys) {
            this.name = name;
            this.startupDistance = startupDistance;
            this.transactions = transactions;
            this.maxValue = maxValue;
            this.bigEvery = bigEvery;
            this.bigValue = bigValue;
            this.keys = keys;
        }

        public String toString() {
            return name;
        }
    }

    /** The startup section is the whole stream: the startup pos stays 0. */
    static final Config ALL = new Config("all", 1000000, 30, 200, 0, 0, KEYS);

    /**
     * A short startup distance: the take moves the startup pos and writes index nodes in
     * later records; a start reads a short section and loads the rest when read.
     */
    static final Config TAKE = new Config("take", 300, 50, 200, 0, 0, KEYS);

    /**
     * Big values: records across meta blocks (every 200,000 bytes), and recovery from a
     * meta block that is not the first.
     */
    static final Config META = new Config("meta", 50000, 30, 200, 3, 60000, KEYS);

    /**
     * Long keys (LONG_KEYS), and a startup section of several records: key nodes that point
     * to key nodes, written in many records. In the full set only, not in the unit tests'
     * sample; testFound021_11's.
     */
    static final Config LONG = new Config("long", 5000, 50, 200, 0, 0, LONG_KEYS);

    /** The sample's workloads (the unit tests). */
    static final Config[] CONFIGS = {ALL, TAKE, META};

    /** The full set's workloads (the night tests): also LONG (bergdb 021-11). */
    static final Config[] FULL_CONFIGS = {ALL, TAKE, META, LONG};

    /** A record of the original: its position, its size and its last byte. */
    static final class Record {
        final long tpos;
        final int size;
        final long lastPos;
        final byte[] bytes;     // the record's own bytes, without meta blocks
        /** The nodes' offsets and sizes in the record's bytes. */
        final List<int[]> nodes = new ArrayList<int[]>();
        int endMarker;          // the offset of the node end marker
        int gotDirtyCount;

        Record(long tpos, int size, long lastPos, byte[] bytes) {
            this.tpos = tpos;
            this.size = size;
            this.lastPos = lastPos;
            this.bytes = bytes;
        }

        long startupPos() {
            return Bytes.bytesToLongLE(bytes, 16);
        }

        long topPos() {
            return Bytes.bytesToLongLE(bytes, 24);
        }
    }

    /** A stream written by a workload, and what it holds after each transaction. */
    static final class Original {
        final Config config;
        final long seed;
        byte[] bytes;
        int n;
        long[] tpos;
        long[] lastPos;
        final List<TreeMap<String, byte[]>> states = new ArrayList<TreeMap<String, byte[]>>();
        final List<Record> records = new ArrayList<Record>();

        Original(Config config, long seed) {
            this.config = config;
            this.seed = seed;
        }

        /** The number of transactions whose records end before 'length'. */
        int committed(long length) {
            int k = 0;
            while (k < n && lastPos[k + 1] < length) {
                k++;
            }
            return k;
        }

        Record recordAt(long pos) {
            for (Record r : records) {
                if (pos >= r.tpos && pos <= r.lastPos) {
                    return r;
                }
            }
            return null;
        }

        public String toString() {
            return config + ", seed " + seed;
        }
    }

    /** Runs the workload and returns its stream and states. */
    static Original write(Config c, long seed) {
        Original o = new Original(c, seed);
        Random r = new Random(seed);
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        o.n = c.transactions;
        o.tpos = new long[o.n + 1];
        o.lastPos = new long[o.n + 1];
        TreeMap<String, byte[]> state = new TreeMap<String, byte[]>();
        o.states.add(new TreeMap<String, byte[]>(state));
        try (Db db = Db.builder().testSetup(s).clock(clock)
                .startupDistance(c.startupDistance).start()) {
            for (int i = 1; i <= o.n; i++) {
                clock.setTime(TIME_STEP * i);
                Trans.Builder b = db.trans();
                b.put(COUNTER, Integer.toString(i));
                state.put(COUNTER, StringUtil.toBytes(Integer.toString(i)));
                Set<String> used = new HashSet<String>();
                int ops = r.nextInt(4);
                for (int k = 0; k < ops; k++) {
                    String key = c.keys[r.nextInt(c.keys.length)];
                    if (!used.add(key)) {
                        continue;
                    }
                    if (state.containsKey(key) && r.nextInt(4) == 0) {
                        b.delete(key);
                        state.remove(key);
                    } else {
                        int size = 1 + r.nextInt(c.maxValue);
                        if (c.bigEvery > 0 && k == 0 && i % c.bigEvery == 0) {
                            size = c.bigValue / 2 + r.nextInt(c.bigValue / 2);
                        }
                        byte[] v = new byte[size];
                        r.nextBytes(v);
                        b.put(key, v);
                        state.put(key, v);
                    }
                }
                Trans t = b.build();
                db.execute(t);
                o.tpos[i] = t.tpos;
                o.states.add(new TreeMap<String, byte[]>(state));
            }
        }
        try {
            o.bytes = new byte[(int) s.getLength()];
            s.read(0, o.bytes, 0, o.bytes.length);
        } catch (IOException e) {
            throw new AssertionError(e);
        }
        walk(o);
        for (int i = 1; i <= o.n; i++) {
            Record rec = o.recordAt(o.tpos[i]);
            if (rec == null || rec.tpos != o.tpos[i]) {
                throw new AssertionError(o + ": no record at " + o.tpos[i]);
            }
            o.lastPos[i] = rec.lastPos;
        }
        return o;
    }

    /** Finds the records of the original, and their nodes. */
    static void walk(Original o) {
        long pos = RecoverableStream.META_BLOCK_SIZE;
        while (pos < o.bytes.length) {
            int size = Bytes.bytesToIntLE(o.bytes, (int) pos);
            long last = RecoverableStream.getSpos(pos, size - 1);
            byte[] bytes = new byte[size];
            for (int i = 0; i < size; i++) {
                bytes[i] = o.bytes[(int) RecoverableStream.getSpos(pos, i)];
            }
            Record rec = new Record(pos, size, last, bytes);
            if (bytes[size - 1] != RecoverableStream.LAST_BYTE) {
                throw new AssertionError(o + ": the record at " + pos + " is not committed");
            }
            int off = 32;
            while (true) {
                int nodeSize = Bytes.bytesToIntLE(bytes, off);
                if (nodeSize == 0) {
                    break;
                }
                rec.nodes.add(new int[] {off, nodeSize});
                off += nodeSize;
            }
            rec.endMarker = off;
            rec.gotDirtyCount = Bytes.bytesToIntLE(bytes, off + 4);
            o.records.add(rec);
            pos = RecoverableStream.getSpos(pos, size);
        }
    }

    // ======== The copies ========

    /**
     * A stream for one start of a copy: the copy's bytes, which it does not copy, and what
     * the start appends. Reads from many threads, as AppendOnlyStream allows.
     */
    static final class CopyStream implements AppendOnlyStream {
        private final byte[] base;
        private final int baseLength;
        private byte[] tail;
        private int tailLength;
        /** An append would have passed MAX_APPENDED. */
        private boolean tooMuch;

        CopyStream(byte[] base, int baseLength) {
            this(base, baseLength, new byte[0], 0);
        }

        private CopyStream(byte[] base, int baseLength, byte[] tail, int tailLength) {
            this.base = base;
            this.baseLength = baseLength;
            this.tail = tail;
            this.tailLength = tailLength;
        }

        /** The same bytes, with what was appended, for the next start. */
        synchronized CopyStream reopen() {
            return new CopyStream(base, baseLength, Arrays.copyOf(tail, tailLength), tailLength);
        }

        synchronized boolean tooMuch() {
            return tooMuch;
        }

        /** The bytes that starts on this stream appended. */
        synchronized int appended() {
            return tailLength;
        }

        public synchronized long getLength() {
            return (long) baseLength + tailLength;
        }

        public long getFirstPos() {
            return 0;
        }

        public synchronized void read(long position, byte[] dest, int destOffset, int length)
                throws IOException {
            if (position < 0 || length < 0 || destOffset < 0
                    || destOffset + length > dest.length) {
                throw new IllegalArgumentException("read(" + position + ", " + destOffset
                        + ", " + length + ")");
            }
            if (position + length > getLength()) {
                throw new EOFException("read of " + length + " bytes at " + position
                        + ", length " + getLength());
            }
            for (int i = 0; i < length; i++) {
                long p = position + i;
                dest[destOffset + i] = p < baseLength ? base[(int) p] : tail[(int) (p - baseLength)];
            }
        }

        public synchronized void append(byte[] source, int sourceOffset, int length)
                throws IOException {
            if (length < 0 || sourceOffset < 0 || sourceOffset + length > source.length) {
                throw new IllegalArgumentException("append(" + sourceOffset + ", " + length + ")");
            }
            if ((long) tailLength + length > MAX_APPENDED) {
                // Recovery's zero fill of a damaged size (014-01): stopped, not waited for.
                tooMuch = true;
                throw new IOException("CopyStream: more than " + MAX_APPENDED
                        + " bytes appended");
            }
            if (tailLength + length > tail.length) {
                tail = Arrays.copyOf(tail, Math.max(2 * tail.length, tailLength + length));
            }
            System.arraycopy(source, sourceOffset, tail, tailLength, length);
            tailLength += length;
        }

        public synchronized void pretruncate(long position) {
            if (position < 0 || position > getLength()) {
                throw new IllegalArgumentException("pretruncate(" + position + ")");
            }
            // A cut is the stream's choice; this one keeps every byte.
        }

        public void close() {}
    }

    /**
     * A damaged copy: what was done, and how its bytes are made (when it is checked, so that
     * only the copies being checked take memory), and its length (-1: all of them).
     */
    static final class Copy {
        final String kind;
        final String what;
        final Supplier<byte[]> bytes;
        final int length;
        /** For a truncation: the transactions it must hold; -1 for other damage. */
        final int expected;
        /** An entry of KNOWN if this damage passes undetected by decision, or null. */
        final String known;

        Copy(String kind, String what, Supplier<byte[]> bytes, int length, int expected,
                String known) {
            this.kind = kind;
            this.what = what;
            this.bytes = bytes;
            this.length = length;
            this.expected = expected;
            this.known = known;
        }
    }

    /** What a start of a copy gave. */
    static final class Outcome {
        /** "holds k", "refused", "read failed", "known 015-73", ... ; null if a failure. */
        final String kind;
        final String failure;

        Outcome(String kind, String failure) {
            this.kind = kind;
            this.failure = failure;
        }

        static Outcome ok(String kind) {
            return new Outcome(kind, null);
        }

        static Outcome fail(String failure) {
            return new Outcome(null, failure);
        }
    }

    // ======== The check of one copy ========

    /** Starts the copy, reads it, and checks what it holds. */
    static Outcome check(Original o, Copy c) {
        byte[] bytes = c.bytes.get();
        CopyStream stream = new CopyStream(bytes, c.length < 0 ? bytes.length : c.length);
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(TIME_STEP * (o.n + 5));
        Db db;
        try {
            db = start(o, c, stream, clock);
        } catch (DatabaseNotCreatedException e) {
            if (c.expected > 0) {
                return Outcome.fail("refused, " + e + "; the copy holds " + c.expected
                        + " transactions");
            }
            return refused(c, stream, e);
        } catch (DbException e) {
            if (c.expected >= 0) {
                return Outcome.fail("refused, " + e + "; the copy holds " + c.expected
                        + " transactions");
            }
            return refused(c, stream, e);
        } catch (Throwable e) {
            if (stream.tooMuch() && c.expected < 0) {
                return Outcome.ok("known 014-01: recovery's zero fill passed "
                        + MAX_APPENDED + " bytes");
            }
            return Outcome.fail("the start threw " + show(e));
        }

        Outcome result;
        try {
            result = read(o, c, db);
            if (result.failure == null && c.expected >= 0) {
                result = startAgain(o, c, db, stream, clock, result);
            }
        } catch (Throwable e) {
            result = Outcome.fail("threw " + show(e));
        }
        result = close(c, db, result);
        if (result.failure != null && stream.tooMuch() && c.expected < 0) {
            // The zero fill, appended by the storage's thread after the start.
            return Outcome.ok("known 014-01: recovery's zero fill passed "
                    + MAX_APPENDED + " bytes");
        }
        return result;
    }

    /**
     * For a truncation: one more transaction, a close, and a start again with it, which
     * must hold the copy's transactions and the new one, and pass the audit.
     */
    private static Outcome startAgain(Original o, Copy c, Db db, CopyStream stream,
            CoreTestClock clock, Outcome result) {
        clock.setTime(TIME_STEP * (o.n + 10));
        db.execute(db.trans().put("/after", "1"));
        db.close();
        TreeMap<String, byte[]> after = new TreeMap<String, byte[]>(o.states.get(c.expected));
        after.put("/after", StringUtil.toBytes("1"));
        CoreTestClock clock2 = new CoreTestClock();
        clock2.setTime(TIME_STEP * (o.n + 20));
        Db again = start(o, c, stream.reopen(), clock2);
        Outcome out = result;
        try {
            String diff = compare(again, o.config, after, Long.MAX_VALUE);
            if (diff != null) {
                out = Outcome.fail("after one more transaction and a start: " + diff);
            } else {
                List<String> audit = Audit.check(again);
                if (!audit.isEmpty()) {
                    out = Outcome.fail("the audit after a start again: " + audit);
                }
            }
        } catch (Throwable e) {
            out = Outcome.fail("after one more transaction and a start: " + show(e));
        }
        return close(c, again, out);
    }

    /**
     * Closes db. A close that throws fails the check, but a DbException after other damage
     * was found by a read: the failed database reports its failure.
     */
    private static Outcome close(Copy c, Db db, Outcome result) {
        try {
            db.close();
        } catch (Throwable e) {
            boolean reported = c.expected < 0 && e instanceof DbException
                    && result.kind != null && result.kind.startsWith("read failed");
            if (result.failure == null && !reported) {
                return Outcome.fail("close() threw " + show(e));
            }
        }
        return result;
    }

    private static Outcome refused(Copy c, CopyStream stream, DbException e) {
        if (stream.tooMuch() && c.expected < 0) {
            return Outcome.ok("known 014-01: recovery's zero fill passed "
                    + MAX_APPENDED + " bytes");
        }
        if (stream.appended() > 0 && c.expected >= 0) {
            return Outcome.fail("refused, " + e + ", after writing " + stream.appended()
                    + " bytes");
        }
        if (stream.appended() > 0) {
            // Recovery wrote (zero fill), then the start refused: 005-83, now 014-01.
            return Outcome.ok("known 014-01: refused (" + e.getClass().getSimpleName()
                    + ") after writing");
        }
        return Outcome.ok("refused (" + e.getClass().getSimpleName() + ")");
    }

    /**
     * Starts a database on the stream; with the audit for a truncation, which must pass it,
     * and without for other damage, where the audit's own reads would meet the damage first.
     */
    private static Db start(Original o, Copy c, AppendOnlyStream stream, CoreTestClock clock) {
        return Db.builder().testSetup(stream).clock(clock)
                .audit(c.expected >= 0 ? AUDIT_EVERY : 0)
                .startupDistance(o.config.startupDistance).start();
    }

    /**
     * Reads the started copy: the counter, then every key now and at the times of the
     * transactions; compares with the original's states.
     */
    static Outcome read(Original o, Copy c, Db db) {
        int k;
        try {
            byte[] counter = DbUtil.get(db, Long.MAX_VALUE, COUNTER);
            k = counter == null ? 0 : parseCounter(counter);
            if (k < 0 || k > o.n) {
                return undetected(c, "the counter is " + show(counter));
            }
            if (c.expected >= 0 && k != c.expected) {
                return Outcome.fail("holds " + k + " transactions, not " + c.expected);
            }
            String diff = compare(db, o.config, o.states.get(k), Long.MAX_VALUE);
            if (diff != null) {
                return undetected(c, "holds " + k + " transactions by the counter, and " + diff);
            }
            for (int j = 1; j <= k; j++) {
                byte[] v = DbUtil.get(db, TIME_STEP * j, COUNTER);
                if (v == null || parseCounter(v) != j) {
                    return undetected(c, "the counter at time " + TIME_STEP * j + " is "
                            + show(v) + ", not " + j);
                }
            }
            for (int j = 1; j <= k; j += 1 + k / 4) {
                diff = compare(db, o.config, o.states.get(j), TIME_STEP * j);
                if (diff != null) {
                    return undetected(c, "at time " + TIME_STEP * j + ", " + diff);
                }
            }
        } catch (DbException e) {
            if (c.expected >= 0) {
                return Outcome.fail("a read threw " + show(e));
            }
            // P7: the database must be failed, and say so.
            try {
                DbUtil.get(db, Long.MAX_VALUE, COUNTER);
                return Outcome.fail("a read threw " + show(e) + ", and the database goes on");
            } catch (IllegalDbStateException expected) {
                return Outcome.ok("read failed (" + e.getClass().getSimpleName() + ")");
            } catch (Throwable t) {
                return Outcome.fail("a read threw " + show(e) + ", and the next " + show(t));
            }
        } catch (Throwable e) {
            return Outcome.fail("a read threw " + show(e));
        }
        if (c.expected >= 0) {
            List<String> audit = Audit.check(db);
            if (!audit.isEmpty()) {
                return Outcome.fail("the audit: " + audit);
            }
        }
        return Outcome.ok(k == o.n ? "holds all" : "holds a prefix");
    }

    private static Outcome undetected(Copy c, String what) {
        if (c.expected >= 0) {
            return Outcome.fail(what);
        }
        if (c.known != null) {
            return Outcome.ok("known " + c.known + ": undetected");
        }
        if (c.kind.equals("node")) {
            // A node changed with its checksum made right is a valid node: outside the fault
            // model (bergdb 017-08); only a crash or a database that goes on is a fault here.
            return Outcome.ok("undetected, its checksum made right");
        }
        return Outcome.fail("undetected: " + what);
    }

    /**
     * null if db holds 'state' at 'time' for COUNTER and the config's keys, else the first
     * difference.
     */
    static String compare(Db db, Config config, Map<String, byte[]> state, long time) {
        List<String> keys = new ArrayList<String>(Arrays.asList(config.keys));
        keys.add(COUNTER);
        keys.add("/after");
        for (String key : keys) {
            byte[] v = DbUtil.get(db, time, key);
            if (!Arrays.equals(v, state.get(key))) {
                return key + " is " + show(v) + ", not " + show(state.get(key));
            }
        }
        return null;
    }

    private static int parseCounter(byte[] v) {
        try {
            return Integer.parseInt(StringUtil.toString(v));
        } catch (NumberFormatException e) {
            return -1;
        }
    }

    static String show(byte[] v) {
        if (v == null) {
            return "null";
        }
        if (v.length <= 8) {
            return "\"" + StringUtil.toString(v) + "\"";
        }
        return v.length + " bytes";
    }

    static String show(Throwable e) {
        StackTraceElement[] st = e.getStackTrace();
        String at = st.length == 0 ? "" : " (at " + st[0].getClassName().replace("bergdb.", "")
                + "." + st[0].getMethodName() + ":" + st[0].getLineNumber() + ")";
        String cause = e.getCause() == null ? "" : ", caused by " + e.getCause();
        return e + at + cause;
    }

    // ======== The damage ========

    /** The copies truncated at each length in 'lengths'. */
    static void truncations(Original o, Iterable<Integer> lengths, List<Copy> out) {
        for (int length : lengths) {
            out.add(new Copy("truncation", "cut at " + length, () -> o.bytes, length,
                    o.committed(length), null));
        }
    }

    /** Every length from 0 to the stream's. */
    static List<Integer> everyLength(Original o) {
        List<Integer> list = new ArrayList<Integer>();
        for (int i = 0; i <= o.bytes.length; i++) {
            list.add(i);
        }
        return list;
    }

    /**
     * A sample of lengths: around each record's start and end and each meta block, and
     * 'random' more.
     */
    static List<Integer> sampleLengths(Original o, Random r, int random) {
        Set<Integer> set = new HashSet<Integer>();
        for (Record rec : o.records) {
            for (int d = -1; d <= 1; d++) {
                set.add((int) rec.tpos + d);
                set.add((int) rec.tpos + 4 + d);
                set.add((int) rec.tpos + 32 + d);
                set.add((int) rec.lastPos + d);
                set.add((int) rec.lastPos + 1 + d);
            }
        }
        for (long mb = 0; mb < o.bytes.length; mb += RecoverableStream.META_BLOCK_DISTANCE) {
            for (int d = -2; d <= RecoverableStream.META_BLOCK_SIZE + 2; d += 7) {
                set.add((int) mb + d);
            }
        }
        for (int i = 0; i < random; i++) {
            set.add(r.nextInt(o.bytes.length + 1));
        }
        List<Integer> list = new ArrayList<Integer>();
        for (int x : set) {
            if (x >= 0 && x <= o.bytes.length) {
                list.add(x);
            }
        }
        java.util.Collections.sort(list);
        return list;
    }

    static final int[] MASKS = {0x01, 0x80, 0xff};

    /** A byte flipped (xor 'mask') at each position. */
    static void flips(Original o, Iterable<Integer> positions, int[] masks, List<Copy> out) {
        for (int p : positions) {
            String where = region(o, p);
            for (int mask : masks) {
                out.add(new Copy("flip", "xor " + mask + " at " + p + " (" + where + ")",
                        () -> {
                            byte[] b = o.bytes.clone();
                            b[p] ^= (byte) mask;
                            return b;
                        }, -1, -1, flipKnown(where, mask)));
            }
        }
    }

    /**
     * The entry of KNOWN that a byte flipped by 'mask' at 'where' (a region) belongs to if
     * it passes undetected, or null: 019-30 in a record's time or topPos, 019-33 by 0xff in
     * a node.
     */
    static String flipKnown(String where, int mask) {
        if (where.endsWith(": time") || where.endsWith(": topPos")) {
            return "019-30";
        }
        if (mask == 0xff && where.contains(": node at offset")) {
            return "019-33";
        }
        return null;
    }

    /** Every position of the stream. */
    static List<Integer> everyPosition(Original o) {
        List<Integer> list = new ArrayList<Integer>();
        for (int i = 0; i < o.bytes.length; i++) {
            list.add(i);
        }
        return list;
    }

    /** The headers of the records, and 'random' positions more. */
    static List<Integer> samplePositions(Original o, Random r, int random) {
        Set<Integer> set = new HashSet<Integer>();
        for (Record rec : o.records) {
            for (int i = 0; i < 32; i += 1 + r.nextInt(4)) {
                set.add((int) rec.tpos + i);
            }
            set.add((int) rec.lastPos);
        }
        for (int i = 0; i < random; i++) {
            set.add(r.nextInt(o.bytes.length));
        }
        List<Integer> list = new ArrayList<Integer>(set);
        java.util.Collections.sort(list);
        return list;
    }

    /** What the byte at 'pos' is: for the report of a failure. */
    static String region(Original o, long pos) {
        if (pos % RecoverableStream.META_BLOCK_DISTANCE < RecoverableStream.META_BLOCK_SIZE) {
            return "meta block";
        }
        Record rec = o.recordAt(pos);
        if (rec == null) {
            return "no record";
        }
        // The meta blocks between the record's start and pos are not its bytes.
        long blocks = pos / RecoverableStream.META_BLOCK_DISTANCE
                - rec.tpos / RecoverableStream.META_BLOCK_DISTANCE;
        int off = (int) (pos - rec.tpos - blocks * RecoverableStream.META_BLOCK_SIZE);
        String in = "record at " + rec.tpos + ", offset " + off + ": ";
        if (off < 4) return in + "size";
        if (off < 5) return in + "format";
        if (off < 8) return in + "unused";
        if (off < 16) return in + "time";
        if (off < 24) return in + "startupPos";
        if (off < 32) return in + "topPos";
        for (int[] node : rec.nodes) {
            if (off < node[0] + node[1]) {
                int o2 = off - node[0];
                return in + "node at offset " + node[0] + " of size " + node[1] + ", its byte "
                        + o2 + (o2 < 4 ? " (size)" : o2 == 6 || o2 == 7 ? " (checksum)" : "");
            }
        }
        if (off < rec.endMarker + 4) return in + "node end marker";
        if (off < rec.endMarker + 8) return in + "got-dirty count";
        if (off < rec.endMarker + 8 + 16 * rec.gotDirtyCount) return in + "got-dirty list";
        if (off == rec.size - 1) return in + "last byte";
        return in + "padding";
    }

    /** A copy with 'data' written at offset 'off' of the record's own bytes. */
    static Copy patched(Original o, String kind, String what, Record rec, int off, byte[] data,
            String known) {
        return new Copy(kind, what, () -> {
            byte[] b = o.bytes.clone();
            writeInRecord(b, rec, off, data);
            return b;
        }, -1, -1, known);
    }

    /** Writes 'data' at offset 'off' of the record's own bytes, in the stream's 'b'. */
    static void writeInRecord(byte[] b, Record rec, int off, byte[] data) {
        for (int i = 0; i < data.length; i++) {
            b[(int) RecoverableStream.getSpos(rec.tpos, off + i)] = data[i];
        }
    }

    private static byte[] le8(long x) {
        byte[] b = new byte[8];
        Bytes.longToBytesLE(x, b, 0);
        return b;
    }

    private static byte[] le4(int x) {
        byte[] b = new byte[4];
        Bytes.intToBytesLE(x, b, 0);
        return b;
    }

    /** The record's size field, its time, startupPos, topPos and got-dirty entries set. */
    static void headerFields(Original o, Record rec, List<Copy> out) {
        List<Record> recs = o.records;
        int index = recs.indexOf(rec);
        Set<Long> sizes = new HashSet<Long>();
        for (int j = index + 1; j < recs.size(); j++) {
            // A size that ends on a later record's last byte, as R6-F1's probe (015-72).
            Record later = recs.get(j);
            long bytes = 0;
            for (int m = index; m <= j; m++) {
                bytes += recs.get(m).size;
            }
            sizes.add(bytes);
            sizes.add(later.lastPos + 1 - rec.tpos);
        }
        for (long s : new long[] {0, 5, 8, 16, 17, 40, 41, rec.size - 8, rec.size + 8,
                rec.size + 1, 2L * rec.size, 1 << 20, Integer.MAX_VALUE - 7, Integer.MAX_VALUE,
                -8, Integer.MIN_VALUE}) {
            sizes.add(s);
        }
        sizes.remove((long) rec.size);
        for (long s : sizes) {
            out.add(patched(o, "header", "size " + s + " (was " + rec.size + ") of the record at "
                    + rec.tpos, rec, 0, le4((int) s), null));
        }

        long tt = Bytes.bytesToLongLE(rec.bytes, 8);
        for (long t : new long[] {tt - 1, tt + 1, tt - TIME_STEP, tt + TIME_STEP, 0, -1,
                Klong.MAX_TIME, Klong.MAX_TIME + 1, Long.MAX_VALUE, Long.MIN_VALUE,
                tt ^ (1L << 40)}) {
            // 019-30: a time that passes the start's checks is taken.
            out.add(patched(o, "header", "time " + t + " (was " + tt + ") of the record at "
                    + rec.tpos, rec, 8, le8(t), "019-30"));
        }

        long sp = rec.startupPos();
        Set<Long> sps = new HashSet<Long>();
        for (Record other : recs) {
            sps.add(other.tpos);
            sps.add(other.tpos + 8);
        }
        for (long x : new long[] {0, 8, 120, 128, -8, Long.MIN_VALUE, Long.MAX_VALUE & ~7L,
                sp | (1L << 40), (long) o.bytes.length, (long) o.bytes.length + 8}) {
            sps.add(x);
        }
        sps.remove(sp);
        for (long x : sps) {
            // 015-73: the start of another record, which the take never reached, passes.
            boolean recordStart = false;
            for (Record other : recs) {
                recordStart |= other.tpos == x;
            }
            out.add(patched(o, "header", "startupPos " + x + " (was " + sp
                    + ") of the record at " + rec.tpos, rec, 16, le8(x),
                    recordStart && x > sp ? "015-73" : null));
        }

        long top = rec.topPos();
        Set<Long> tops = new HashSet<Long>();
        for (Record other : recs) {
            for (int[] node : other.nodes) {
                tops.add(RecoverableStream.getSpos(other.tpos, node[0]));
            }
            tops.add(other.tpos);
        }
        for (long x : new long[] {0, -1, 8, top + 8, top - 8, top | (1L << 40), Long.MAX_VALUE}) {
            tops.add(x);
        }
        tops.remove(top);
        for (long x : tops) {
            // 019-30: a topPos that passes the start's checks, such as an older version of
            // the top node before the startup section, is taken.
            out.add(patched(o, "header", "topPos " + x + " (was " + top + ") of the record at "
                    + rec.tpos, rec, 24, le8(x), "019-30"));
        }

        int list = rec.endMarker + 8;
        for (int e = 0; e < rec.gotDirtyCount; e++) {
            int at = list + 16 * e;
            long id = Bytes.bytesToLongLE(rec.bytes, at);
            long pos = Bytes.bytesToLongLE(rec.bytes, at + 8);
            for (long x : new long[] {id + 1, id - 1, 0, -1, 123456789L, Long.MAX_VALUE}) {
                out.add(patched(o, "header", "got-dirty id " + x + " (was " + id + ", entry " + e
                        + ") of the record at " + rec.tpos, rec, at, le8(x), null));
            }
            Set<Long> poses = new HashSet<Long>();
            for (long x : new long[] {pos + 8, pos - 8, 0, -1, 8, Long.MAX_VALUE}) {
                poses.add(x);
            }
            for (Record other : recs) {
                for (int[] node : other.nodes) {
                    poses.add(RecoverableStream.getSpos(other.tpos, node[0]));
                }
            }
            poses.remove(pos);
            for (long x : poses) {
                out.add(patched(o, "header", "got-dirty position " + x + " (was " + pos
                        + ", entry " + e + ") of the record at " + rec.tpos, rec, at + 8,
                        le8(x), null));
            }
        }
        for (int x : new int[] {rec.gotDirtyCount + 1, rec.gotDirtyCount - 1, -1,
                Integer.MAX_VALUE, 1 << 20}) {
            if (x == rec.gotDirtyCount) continue;
            out.add(patched(o, "header", "got-dirty count " + x + " (was " + rec.gotDirtyCount
                    + ") of the record at " + rec.tpos, rec, rec.endMarker + 4, le4(x), null));
        }
    }

    /**
     * A node's bytes changed and its checksum made right (Fletcher-16, NodeChecksum): each
     * byte up to 'maxOffset' xor each mask, and each 4-byte field set to 'values'.
     */
    static void nodeFields(Original o, Record rec, int maxOffset, int[] masks, int[] values,
            List<Copy> out) {
        for (int[] node : rec.nodes) {
            int start = node[0];
            int size = node[1];
            for (int i = 0; i < Math.min(size, maxOffset); i++) {
                if (i == 6 || i == 7) {
                    continue;   // the checksum
                }
                for (int mask : masks) {
                    byte[] nb = Arrays.copyOfRange(rec.bytes, start, start + size);
                    nb[i] ^= (byte) mask;
                    out.add(nodeCopy(o, rec, node, nb, "xor " + mask + " at its byte " + i));
                }
            }
            for (int i = 0; i + 4 <= Math.min(size, maxOffset); i += 4) {
                if (i == 4) {
                    continue;   // type, format and checksum
                }
                for (int v : values) {
                    byte[] nb = Arrays.copyOfRange(rec.bytes, start, start + size);
                    if (Bytes.bytesToIntLE(nb, i) == v) continue;
                    Bytes.intToBytesLE(v, nb, i);
                    out.add(nodeCopy(o, rec, node, nb, "int " + v + " at its byte " + i));
                }
            }
        }
    }

    private static Copy nodeCopy(Original o, Record rec, int[] node, byte[] nb, String what) {
        Bytes.ushortToBytesLE(NodeChecksum.sumWithZeroReplace(nb, 0, nb.length, 6), nb, 6);
        return patched(o, "node", what + ", checksum right, of the node at offset " + node[0]
                + " (size " + node[1] + ", type " + nb[4] + ") of the record at " + rec.tpos,
                rec, node[0], nb, null);
    }

    /**
     * The bytes from 'from' to 'to' cut out of the stream. If it passes undetected, it is
     * 019-31's: nothing links a record to the one before it.
     */
    static Copy cutOut(Original o, int from, int to) {
        return new Copy("cut out", "bytes " + from + " to " + to + " cut out", () -> {
            byte[] b = new byte[o.bytes.length - (to - from)];
            System.arraycopy(o.bytes, 0, b, 0, from);
            System.arraycopy(o.bytes, to, b, from, o.bytes.length - to);
            return b;
        }, -1, -1, "019-31");
    }

    /** Ranges cut out: whole records (pairs of record starts), and 'random' ranges. */
    static void cuts(Original o, Random r, int maxPairs, int random, List<Copy> out) {
        List<Integer> starts = new ArrayList<Integer>();
        for (Record rec : o.records) {
            starts.add((int) rec.tpos);
        }
        starts.add(o.bytes.length);
        int pairs = 0;
        for (int i = 0; i < starts.size() && pairs < maxPairs; i++) {
            for (int j = i + 1; j < starts.size() && pairs < maxPairs; j++) {
                if (j - i <= 3 || r.nextInt(4) == 0) {
                    out.add(cutOut(o, starts.get(i), starts.get(j)));
                    pairs++;
                }
            }
        }
        for (int i = 0; i < random; i++) {
            int a = RecoverableStream.META_BLOCK_SIZE + r.nextInt(o.bytes.length - 128);
            int len = 1 + r.nextInt(Math.min(2000, o.bytes.length - a));
            if (r.nextBoolean()) {
                len = (len + 7) / 8 * 8;
                a = a / 8 * 8;
                len = Math.min(len, o.bytes.length - a);
            }
            out.add(cutOut(o, a, a + len));
        }
    }

    // ======== Runs ========

    /** The results of a run: outcomes by kind, the failures. */
    static final class Results {
        final Map<String, Integer> counts = new TreeMap<String, Integer>();
        final List<String> failures = new ArrayList<String>();
        final List<String> skipped = new ArrayList<String>();
        int copies;

        void add(String kind, int n) {
            Integer c = counts.get(kind);
            counts.put(kind, (c == null ? 0 : c) + n);
        }
    }

    /** Checks the copies, on 'threads' threads; each must end within 'seconds'. */
    static void checkAll(final Original o, List<Copy> copies, int threads, int seconds,
            Results results) {
        ExecutorService pool = Executors.newFixedThreadPool(threads, new ThreadFactory() {
            public Thread newThread(Runnable r) {
                Thread t = new Thread(r, "CorruptStreamTester");
                t.setDaemon(true);
                return t;
            }
        });
        try {
            List<Future<Outcome>> futures = new ArrayList<Future<Outcome>>();
            for (final Copy c : copies) {
                futures.add(pool.submit(() -> check(o, c)));
            }
            for (int i = 0; i < copies.size(); i++) {
                Copy c = copies.get(i);
                Outcome out;
                try {
                    out = futures.get(i).get(seconds, TimeUnit.SECONDS);
                } catch (TimeoutException e) {
                    out = Outcome.fail("the start or the reads did not end in " + seconds + " s");
                } catch (Exception e) {
                    out = Outcome.fail("the check threw " + e);
                }
                results.copies++;
                String entry = out.failure == null ? null : entryOf(c, out.failure);
                if (out.failure == null) {
                    results.add(c.kind + ": " + out.kind, 1);
                } else if (entry != null && skips(entry)) {
                    results.add(c.kind + ": known fault " + entry + ", skipped", 1);
                    results.skipped.add(o + ", " + c.kind + ", " + c.what + ": " + out.failure);
                } else {
                    results.add(c.kind + ": FAILED", 1);
                    results.failures.add(o + ", " + c.kind + ", " + c.what + ": " + out.failure);
                    if (out.failure.contains("did not end")) {
                        break;      // the thread may never end; the rest would wait for it
                    }
                }
            }
        } finally {
            pool.shutdownNow();
        }
    }

    /**
     * One run on an original of each configuration: 'full' every truncation, every byte
     * flipped by each mask, each record's header fields and each node's fields, on
     * FULL_CONFIGS; otherwise a sample, on CONFIGS. Returns the results; prints a summary to
     * 'out'.
     */
    static Results run(long seed, boolean full, int threads, PrintStream out) {
        Results results = new Results();
        Random r = new Random(seed);
        for (Config c : full ? FULL_CONFIGS : CONFIGS) {
            Original o = write(c, seed * 31 + c.name.hashCode());
            List<Copy> copies = new ArrayList<Copy>();
            boolean every = full && o.bytes.length < 100000;
            truncations(o, every ? everyLength(o) : sampleLengths(o, r, full ? 20000 : 60),
                    copies);
            checkAll(o, copies, threads, 60, results);

            copies.clear();
            flips(o, full && every ? everyPosition(o) : samplePositions(o, r, full ? 5000 : 60),
                    full ? MASKS : new int[] {MASKS[r.nextInt(MASKS.length)]}, copies);
            checkAll(o, copies, threads, 60, results);

            copies.clear();
            List<Record> recs = new ArrayList<Record>();
            if (full) {
                recs.addAll(o.records);
            } else {
                recs.add(o.records.get(o.records.size() - 1));
                recs.add(o.records.get(r.nextInt(o.records.size())));
            }
            for (Record rec : recs) {
                headerFields(o, rec, copies);
            }
            checkAll(o, copies, threads, 60, results);

            copies.clear();
            for (Record rec : recs) {
                nodeFields(o, rec, full ? 64 : 40, full ? MASKS : new int[] {0x80},
                        new int[] {-8, 0x7ffffff8, 0x10000}, copies);
            }
            if (!full) {
                // A sample: every 7th, from a random one.
                List<Copy> some = new ArrayList<Copy>();
                for (int i = r.nextInt(7); i < copies.size(); i += 7) {
                    some.add(copies.get(i));
                }
                copies = some;
            }
            checkAll(o, copies, threads, 60, results);

            copies.clear();
            cuts(o, r, full ? 400 : 30, full ? 400 : 30, copies);
            checkAll(o, copies, threads, 60, results);
            out.println("CorruptStreamTester: " + o + ", " + o.bytes.length + " bytes, "
                    + o.records.size() + " records");
        }
        out.println("CorruptStreamTester: seed " + seed + (full ? ", full" : ", a sample")
                + ", " + results.copies + " copies");
        for (Map.Entry<String, Integer> e : results.counts.entrySet()) {
            out.println("  " + e.getValue() + "\t" + e.getKey());
        }
        int shown = 0;
        for (String f : results.skipped) {
            if (shown++ < 5) {
                out.println("  Known fault, skipped: " + f);
            }
        }
        shown = 0;
        for (String f : results.failures) {
            if (shown++ < 30) {
                out.println("  FAILED: " + f);
            }
        }
        return results;
    }

    static void assertNoFailure(Results results) {
        if (!results.failures.isEmpty()) {
            throw new AssertionError(results.failures.size() + " copies failed, the first: "
                    + results.failures.get(0));
        }
    }

    // ======== Tests ========

    /**
     * The copies that found 019-32 (2026-11-06; bergdb 018-07, section 6), each now refused,
     * a read that fails the database, or what the original held (check). Before 019-32's
     * fix, each failed: a start or a read threw an AssertionError or a ClassCastException.
     * A row: the workload, the Original's seed, the record, then the node's offset in it,
     * its byte and the xor (its checksum made right); or -1, the stream's byte and the xor.
     */
    @Nano
    public static void testFound019_32() {
        Object[][] rows = {
            {META, 3348004L, 365024, 104, 39, 0x80},    // a klong of type 2, at the start
            {TAKE, 3552484L, 31880, 156, 37, 0x80},     // a value node's key, at the start
            {TAKE, 4184729L, 2808, 72, 17, 0x01},       // a key count, at a read
            {TAKE, 4184729L, 2808, 72, 24, 0x01},       // a key node's id 0 to 1, at a read
            {TAKE, 4184729L, 2808, 32, 16, 0x01},       // a top node's id 1 to 0, at a read
            {ALL, 729011L, 4528, 72, 16, 0x01},         // a leaf's flag, at the start
            {ALL, 729042L, 128, 72, 16, 0x01},          // the flag of a leaf without keys
            {META, 3980311L, 180568, 88, 56, 0x80},     // a skip pointer to a key node
            {TAKE, 4184729L, 2808, -1, 3151, 0xff},     // a value pointer negative, a read
            {TAKE, 4184729L, 2808, -1, 3336, 0xff},     // a value pointer odd, a read
        };
        Map<String, Original> originals = new TreeMap<String, Original>();
        for (Object[] row : rows) {
            Config config = (Config) row[0];
            long seed = (Long) row[1];
            Original o = originals.computeIfAbsent(config.name + seed, k -> write(config, seed));
            int offset = (Integer) row[3], at = (Integer) row[4], mask = (Integer) row[5];
            Copy c;
            if (offset < 0) {
                List<Copy> out = new ArrayList<Copy>();
                flips(o, Arrays.asList(at), new int[] {mask}, out);
                c = out.get(0);
            } else {
                Record rec = o.recordAt((Integer) row[2]);
                int[] node = null;
                for (int[] n : rec.nodes) {
                    if (n[0] == offset) node = n;
                }
                byte[] nb = Arrays.copyOfRange(rec.bytes, node[0], node[0] + node[1]);
                nb[at] ^= (byte) mask;
                c = nodeCopy(o, rec, node, nb, "xor " + mask + " at its byte " + at);
            }
            Outcome out = check(o, c);
            if (out.failure != null) {
                throw new AssertionError(config.name + ", seed " + seed + ", " + c.what + ": "
                        + out.failure);
            }
        }
    }

    /**
     * A pointer that a start links by node id, set to a version of a node of another type,
     * its node's checksum made right (bergdb 021-11): each refused at the start. Before, the
     * start's rule 4 (NodeCollection.linkToCanonical) gave the pointer that node's handle,
     * and a read threw an AssertionError ("Expected a KeyNode") or a ClassCastException, or
     * the check of rule 4 (005-57), which runs with -ea, threw an AssertionError (without
     * -ea, a read fails). A row: the record of LONG's original of seed 1, the node's offset
     * in it, the pointer's byte in the node, the position it is set to.
     */
    @Nano
    public static void testFound021_11() {
        long[][] rows = {
            {32760, 880, 112, 35936},   // a key node's pointer 1 to the newest top node
            {35904, 32, 40, 7080},      // a top node's skip pointer 0 to a key node
            {32760, 880, 112, 27560},   // to an older top node version: 005-57's check (-ea)
        };
        Original o = write(LONG, 1);
        for (long[] row : rows) {
            Record rec = o.recordAt(row[0]);
            int[] node = null;
            for (int[] n : rec.nodes) {
                if (n[0] == row[1]) node = n;
            }
            byte[] nb = Arrays.copyOfRange(rec.bytes, node[0], node[0] + node[1]);
            Bytes.longToBytesLE(row[3], nb, (int) row[2]);
            Copy c = nodeCopy(o, rec, node, nb, "its byte " + row[2] + " set to " + row[3]);
            Outcome out = check(o, c);
            if (out.failure != null || !out.kind.startsWith("refused")) {
                throw new AssertionError(c.what + ": " + (out.failure != null ? out.failure
                        : out.kind));
            }
        }
    }

    /**
     * A key node that a start reads from before the startup section, damaged so that it
     * breaks KeyNode's invariants (bergdb 021-12): each copy refused at the start. Before, the
     * start threw an AssertionError: its check of the nodes in memory (KeyNode.check, from
     * DbStarter.postStartupCheck, also without -ea), or an assert of KeyNode.addKlong when the
     * rerun put into the node. Copies of LONG's first full run (seed 20766), in its node at
     * offset 200 of the record at 36336.
     */
    @Nano
    public static void testFound021_12() {
        Original o = write(LONG, 20766L * 31 + LONG.name.hashCode());
        Record rec = o.recordAt(36336);
        int[] node = null;
        for (int[] n : rec.nodes) {
            if (n[0] == 200) node = n;
        }
        List<Copy> copies = new ArrayList<Copy>();
        // A time klong's byte flipped by 0xff (019-33's flip): the times not increasing, at
        // the start's check (36570), and at the rerun's put (36738).
        flips(o, Arrays.asList(36570, 36738), new int[] {0xff}, copies);
        // The first klong, a time klong, made a key klong, whose pointer is Spos.NULL.
        byte[] nb = Arrays.copyOfRange(rec.bytes, node[0], node[0] + node[1]);
        Bytes.intToBytesLE(0x7ffffff8, nb, 36);
        copies.add(nodeCopy(o, rec, node, nb, "int " + 0x7ffffff8 + " at its byte 36"));
        for (Copy c : copies) {
            Outcome out = check(o, c);
            if (out.failure != null || !out.kind.startsWith("refused")) {
                throw new AssertionError(c.what + ": " + (out.failure != null ? out.failure
                        : out.kind));
            }
        }
    }

    /** A sample on a fixed seed: the unit tests. */
    @Nano
    public static void testSample(TestEnvironment c) {
        assertNoFailure(run(1, false, 2, c.out()));
    }

    /**
     * The full set for the night tests: every truncation of the streams under 100 KB, every
     * byte flipped, every record's header fields and every node's fields; a new seed each
     * day (the day's number), printed.
     */
    @Nano("night")
    public static void testFull(TestEnvironment c) {
        long seed = System.currentTimeMillis() / 86400000L;
        assertNoFailure(run(seed, true, 4, c.out()));
    }

    /** Usage: CorruptStreamTester [SEED [full [THREADS]]]. */
    public static void main(String[] args) {
        long seed = args.length > 0 ? Long.parseLong(args[0]) : 1;
        boolean full = args.length > 1 && args[1].equals("full");
        int threads = args.length > 2 ? Integer.parseInt(args[2]) : 4;
        long t0 = System.nanoTime();
        Results results = run(seed, full, threads, System.out);
        System.out.println("CorruptStreamTester: " + (System.nanoTime() - t0) / 1000000 + " ms, "
                + results.failures.size() + " failures");
        System.exit(results.failures.isEmpty() ? 0 : 1);
    }
}
