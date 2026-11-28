package bergdb.core;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.TreeMap;
import java.util.concurrent.atomic.AtomicLong;

import bergdb.dag.Keys;
import bergdb.dag.Klong;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.util.Clock;
import bergdb.pub.util.DbException;
import bergdb.pub.util.DbFailedException;
import bergdb.stream.CutStream;

/**
 * Harness 6.4 of release 2026.3, sizes and times at their limits (bergdb 018-01, section
 * 6.4; bergdb 018-06). Random transactions of the Core Layer at the edge of every limit:
 * values whose nodes take StoredTrans.valueLimit() and a few bytes more or less, alone and
 * together, long keys, value transformations that grow a value, times at the last time
 * (Klong.MAX_TIME; the last user time until bergdb 031-06) and past it, a clock out of
 * range or going back, and settings at their bounds;
 * with reclaim (a retain duration of one second) and eviction (small budgets) on, and
 * restarts. The record limit is lowered, as StoredTrans's own tests do, so that a value at
 * the limit is a few hundred kB.
 *
 * <p>What it checks: each transaction is either refused before its go point, with a
 * DbException for a reason the Javadoc gives (its size, its index nodes, the time), and
 * the database goes on with nothing of it written; or it is committed and every value
 * reads back. A transaction within the limits is committed. The database never fails, and
 * after a restart it holds every committed value and setting and takes commits. Since
 * bergdb 026-06 without exception: a value transformation's result counts as a value given
 * directly, so one that takes the transaction's value nodes above the value limit is
 * refused before the go point. Until then such a result was the caller's fault (018-01,
 * section 6.4; 015-51): a database that failed after one was counted so, and the run
 * ended.</p>
 *
 * <p>Since bergdb 024-24 the limits of 024-17 too: keys of up to 111 bytes, the most (L2),
 * and of 112, which the Trans.Builder call refuses with IllegalArgumentException, nothing
 * written; transactions of up to 1,550 small KVs, those of more than 500 refused with
 * DbException (L1). Until then keys of up to 3,006 bytes, and 1,550 KVs were taken.</p>
 *
 * <p>Each run has a seed, printed at a failure, so that it can be repeated:
 * {@code run(seed, steps)}, or main.</p>
 *
 * @author Frans Lundberg
 */
public class LimitsTester {

    /**
     * The known faults that the harness steps around, so that it passes on main until they
     * are fixed; one line each. A fix makes its line unneeded: remove it. With
     * -Dbergdb.limits.skip=none, nothing is skipped.
     */
    static final String[] SKIP = {
    };

    static boolean skips(String entry) {
        if ("none".equals(System.getProperty("bergdb.limits.skip"))) {
            return false;
        }
        return Arrays.asList(SKIP).contains(entry);
    }

    /** The record limits a run takes, one per run: 240 kB leaves setStartupDistance's 200 kB. */
    static final long[] RECORD_LIMITS = {240 * 1000, 300 * 1000, 1000 * 1000};

    /**
     * The first startup distances, set right after the creation (bergdb 028-13; the
     * builder's until then): the least, 10, and others.
     */
    static final int[] STARTUP_DISTANCES = {10, 2000, 400 * 1000, 2000 * 1000};

    /** Cache size indicators: none evicted, the least, small, larger. */
    static final long[] CACHE_SIZES = {Long.MAX_VALUE, 1, 300 * 1000, 3000 * 1000};

    /**
     * Arguments of setStartupDistance, at and around its clamp (bergdb 015-76; 028-13: 10
     * to 10^9, and below 1 refused).
     */
    static final int[] SD_ARGS = {-1, 0, 9, 10, 399999, 400000, 2000 * 1000,
            1000 * 1000 * 1000, 1000 * 1000 * 1000 + 1, Integer.MAX_VALUE};

    /** Arguments of setRetainDuration: below its least (refused), its least, forever. */
    static final long[] RETAIN_ARGS = {Clock.UNITS_PER_SEC - 1, Clock.UNITS_PER_SEC,
            2 * Clock.UNITS_PER_SEC, 30 * Clock.UNITS_PER_SEC, Long.MAX_VALUE - 1,
            Long.MAX_VALUE};

    /** Arguments of setReclaimInternalFraction: its bounds and outside them (refused). */
    static final double[] FRACTION_ARGS = {0.0009, 0.001, 0.1, 0.25, 0.9, 0.9001, Double.NaN};

    /** Arguments of setCacheSizeIndicator: 0 is refused. */
    static final long[] CACHE_ARGS = {0, 1, 1000, 300 * 1000, 10 * 1000 * 1000,
            Long.MAX_VALUE};

    /** A run's outcome, for the summaries. */
    static final class Result {
        long committed, refusedSize, refusedTime, refusedNodes, refusedClock,
                refusedOrdinals, refusedLimits, settings,
                restarts, cuts, iterations;

        void add(Result o) {
            committed += o.committed;
            refusedSize += o.refusedSize;
            refusedTime += o.refusedTime;
            refusedNodes += o.refusedNodes;
            refusedClock += o.refusedClock;
            refusedOrdinals += o.refusedOrdinals;
            refusedLimits += o.refusedLimits;
            settings += o.settings;
            restarts += o.restarts;
            cuts += o.cuts;
            iterations += o.iterations;
        }

        public String toString() {
            return committed + " committed, refused: " + refusedSize + " size, " + refusedNodes
                    + " index nodes, " + refusedTime + " time, " + refusedClock + " clock, "
                    + refusedOrdinals + " top node ordinals, " + refusedLimits + " limits of "
                    + "024-17; "
                    + settings + " settings calls, " + restarts + " restarts, " + cuts
                    + " cuts, " + iterations + " reclaim iterations";
        }
    }

    /** One run: a database, its reference, and the random choices of its seed. */
    static final class Run {
        final long seed;
        final Random r;
        final int steps;
        final AtomicLong now = new AtomicLong(Clock.UNITS_PER_SEC);
        final Clock clock = () -> now.get();
        final ArrayDeque<String> log = new ArrayDeque<String>();
        final Result result = new Result();

        final long recordLimit;
        final boolean smallNodes;
        final int builderDistance;
        final long cacheSize;
        final boolean evictRandom;
        final int endPhaseAt;          // the step where the clock goes to the last times; -1
        final int faultAt;             // a result above the value limit (026-06); -1: none
        /** The second top node's ordinal, near the last (bergdb 005-02); 0: not given. */
        final long secondOrdinal;

        /** The reference: each key's last value, null for deleted. */
        final TreeMap<String, byte[]> ref = new TreeMap<String, byte[]>();
        int startupDistance;
        long retain = Long.MAX_VALUE;
        int fractionUnits = Reclaim.DEFAULT_INTERNAL_FRACTION;
        long cacheIndicator;

        CutStream stream;
        Db db;
        int step;
        boolean endPhase;
        long lastUserTime = -1;
        /** The largest clock time in range that the database has seen: reads take it too. */
        long maxClock = -1;
        long lastCut;

        Run(long seed, int steps) {
            this.seed = seed;
            this.steps = steps;
            // Mixed: java.util.Random's first values for adjacent seeds are alike, and the
            // night's seeds are adjacent.
            this.r = new Random(new java.util.SplittableRandom(seed).nextLong());
            recordLimit = RECORD_LIMITS[r.nextInt(RECORD_LIMITS.length)];
            smallNodes = r.nextInt(3) == 0;
            builderDistance = STARTUP_DISTANCES[r.nextInt(STARTUP_DISTANCES.length)];
            cacheSize = CACHE_SIZES[r.nextInt(CACHE_SIZES.length)];
            evictRandom = r.nextInt(5) == 0;
            endPhaseAt = r.nextInt(3) == 0 ? steps * 3 / 4 + r.nextInt(steps / 4) : -1;
            faultAt = r.nextInt(4) == 0 ? steps / 2 + r.nextInt(steps / 2) : -1;
            cacheIndicator = cacheSize;
            // A new super root comes only when the tree grows a level, some tens in a run:
            // 1 to 3 before the last ordinal, the end comes within the run.
            secondOrdinal = r.nextInt(8) == 0
                    ? bergdb.dag.TopNode.MAX_TOP_NODE_ID_VALUE - 1 - r.nextInt(3) : 0;
        }

        long valueLimit() {
            return StoredTrans.valueLimit();
        }

        // ======== Starting and stopping ========

        Db start(CutStream s) {
            DbBuilder b = Db.builder().testSetup(s).clock(clock).cacheSizeIndicator(cacheSize);
            if (smallNodes) {
                b.maxNodeSize8();
            }
            if (evictRandom) {
                b.evictionSchedule(Eviction.Schedule.RANDOM, seed);
            }
            if (secondOrdinal > 0) {
                // At every start, as the node size (DbBuilder.secondTopOrdinal).
                b.secondTopOrdinal(secondOrdinal);
            }
            return b.start();
        }

        void startFirst() {
            stream = new CutStream();
            db = start(stream);
            check(db.getStartupDistance() == Db.DEFAULT_STARTUP_DISTANCE, "a new database's "
                    + "startup distance: " + db.getStartupDistance());
            // The first setting, right after the creation (bergdb 028-13).
            check(db.setStartupDistance(builderDistance) == builderDistance,
                    "setStartupDistance(" + builderDistance + ") did not return it");
            startupDistance = db.getStartupDistance();
            note("start: record limit " + recordLimit + ", value limit " + valueLimit()
                    + ", startup distance " + builderDistance + ", cache " + cacheSize
                    + (smallNodes ? ", node size 8" : "") + (evictRandom ? ", evict random" : "")
                    + ", end phase at " + endPhaseAt + ", result over the limit at " + faultAt
                    + (secondOrdinal > 0 ? ", second top ordinal " + secondOrdinal : ""));
            if (r.nextInt(4) != 0) {
                try {
                    db.setRetainDuration(Clock.UNITS_PER_SEC);
                    retain = Clock.UNITS_PER_SEC;
                } catch (DbException e) {
                    check(refusedAtEnd(String.valueOf(e.getMessage())), "setRetainDuration at "
                            + "the start refused: " + e);
                }
            }
        }

        void restart() {
            note("restart");
            result.iterations += db.getReclaimIterationCount();
            db.close();
            stream = stream.copy();
            db = start(stream);
            result.restarts++;
            // The cache size indicator is for the run only; a start takes the builder's.
            cacheIndicator = cacheSize;
            check(db.getStartupDistance() == startupDistance, "the startup distance after a "
                    + "restart: expected " + startupDistance + ", got " + db.getStartupDistance());
            check(db.getRetainDuration() == retain, "the retain duration after a restart: "
                    + "expected " + retain + ", got " + db.getRetainDuration());
            check(db.internal().reclaim().getInternalFractionUnits() == fractionUnits,
                    "the internal fraction after a restart: expected " + fractionUnits
                    + " units, got " + db.internal().reclaim().getInternalFractionUnits());
            checkAll();
        }

        void stop() {
            if (db != null) {
                try {
                    db.close();
                } catch (RuntimeException e) {
                    // A failed database's close reports the failure; it is closed.
                }
                db = null;
            }
        }

        // ======== The checks ========

        void note(String s) {
            log.addLast(step + ": " + s);
            int max = Integer.getInteger("bergdb.limits.lines", 30);
            while (log.size() > max) {
                log.removeFirst();
            }
        }

        void check(boolean ok, String what) {
            if (!ok) {
                fail(what, null);
            }
        }

        void fail(String what, Throwable cause) {
            StringBuilder sb = new StringBuilder();
            sb.append("LimitsTester, seed ").append(seed).append(", step ").append(step)
                    .append(": ").append(what).append("\nThe last calls:\n");
            for (String s : log) {
                sb.append("  ").append(s).append('\n');
            }
            throw new AssertionError(sb.toString(), cause);
        }

        void checkKey(String key) {
            byte[] expected = ref.get(key);
            byte[] actual = DbUtil.get(db, Long.MAX_VALUE, key);
            if (!Arrays.equals(expected, actual)) {
                fail("get(" + key + "): expected " + show(expected) + ", got " + show(actual),
                        null);
            }
        }

        void checkAll() {
            for (String key : ref.keySet()) {
                checkKey(key);
            }
        }

        void checkActive() {
            if (!db.internal().isActive()) {
                // The next call says why.
                try {
                    db.execute(db.trans().put("/check", "x").build());
                } catch (DbFailedException e) {
                    fail("the database failed", e.getCause() != null ? e.getCause() : e);
                } catch (RuntimeException e) {
                    fail("the database is not active", e);
                }
                fail("the database is not active", null);
            }
        }

        void updateCuts() {
            long cut = stream.getCut();
            if (cut > lastCut) {
                lastCut = cut;
                result.cuts++;
            }
        }

        /**
         * True if a transaction may find no time left: the clock, a read's time or the last
         * user transaction's is near the last time, Klong.MAX_TIME, with room for the
         * setters' records (since bergdb 031-06, Q4, every transaction may take a time up to
         * it; until then user transactions stopped 1,024 earlier).
         */
        boolean nearEnd() {
            long t = Math.max(Math.max(now.get(), maxClock), lastUserTime + 1);
            return t > Klong.MAX_TIME - 4096;
        }

        /** A setter's refusal at the end of the times or of the top node ordinals. */
        boolean refusedAtEnd(String m) {
            return m.contains("No database time is left") && nearEnd()
                    || m.contains("used its top node ordinals") && secondOrdinal > 0;
        }

        // ======== Transactions ========

        /** A planned KV of a transaction: value null for a delete. */
        final class Op {
            final String key;
            final byte[] value;
            final ValueTransformation vt;
            byte[] made;               // the transformation's result

            Op(String key, byte[] value, ValueTransformation vt) {
                this.key = key;
                this.value = value;
                this.vt = vt;
            }

            long nodeBytes() {
                return StoredValueNode.getByteSizeLong(value, Keys.toSegments(key));
            }

            public String toString() {
                String k = key.length() <= 40 ? key : key.substring(0, 20) + "...("
                        + key.length() + " chars)";
                return k + (vt != null ? " <- f(" + show(value) + ")" : "=" + show(value));
            }
        }

        /**
         * Executes ops as one transaction, at the clock's time. Returns true if it was
         * committed. callers: a transformation's result above the value limit, refused since
         * bergdb 026-06 (until then the caller's fault, 015-51).
         */
        boolean execute(List<Op> ops, String what, boolean callers) {
            Trans.Builder b = db.trans();
            long bytes = 0;
            boolean keyOver = false;            // a key over L2 (bergdb 024-24)
            for (Op op : ops) {
                keyOver |= Keys.toBytes(op.key).length > Db.MAX_KEY_BYTES;
            }
            try {
                for (Op op : ops) {
                    long[] key = Keys.toSegments(op.key);
                    if (op.vt != null) {
                        b.put(key, null, op.value, op.vt);
                    } else if (op.value == null) {
                        b.delete(key);
                    } else {
                        b.put(key, op.value);
                    }
                    bytes += op.nodeBytes();
                }
            } catch (IllegalArgumentException e) {
                // L2 at the builder's call: nothing of the transaction is written.
                note(what + ": refused by the builder: " + e.getMessage());
                check(keyOver && e.getMessage().contains("(bergdb 024-17, L2)"),
                        what + ": refused by the builder for a reason that does not hold: " + e);
                result.refusedLimits++;
                checkActive();
                for (Op op : ops) {
                    checkKey(op.key);
                }
                return false;
            }
            check(!keyOver, what + ": a key over L2 taken by the builder");
            final long clockTime = now.get();
            final boolean clockOut = clockTime < Klong.MIN_TIME || clockTime > Klong.MAX_TIME;
            final boolean over = bytes > valueLimit();
            final boolean nearEnd = nearEnd();
            note(what + " " + (ops.size() <= 8 ? ops.toString() : ops.size() + " KVs, "
                    + ops.subList(0, 3) + "...") + " (" + bytes + " bytes, clock " + clockTime
                    + ")");
            Trans t = b.build();
            try {
                db.execute(t);
            } catch (DbFailedException e) {
                fail(what + ": the database failed", e.getCause() != null ? e.getCause() : e);
            } catch (DbException e) {
                // Db checks the size first, then under the write lock the top node
                // ordinals, the index nodes and the time: any reason that holds may be
                // the one given.
                String m = String.valueOf(e.getMessage());
                boolean holds;
                if (m.contains("after its value transformations")) {
                    // Db.transformValues (bergdb 026-06): the results' value nodes over the
                    // value limit, as values given directly.
                    holds = madeBytes(ops) > valueLimit();
                    result.refusedSize++;
                } else if (m.contains("outside the range")) {
                    holds = clockOut;
                    result.refusedClock++;
                } else if (m.contains("The transaction is too large: its values")) {
                    holds = over;
                    result.refusedSize++;
                } else if (m.contains("No database time is left")) {
                    holds = nearEnd;
                    result.refusedTime++;
                } else if (m.contains("used its top node ordinals")) {
                    holds = secondOrdinal > 0;
                    result.refusedOrdinals++;
                } else if (m.contains("(bergdb 024-17, L1)")) {
                    holds = ops.size() > Db.MAX_OPERATIONS;
                    result.refusedLimits++;
                } else if (m.contains("index nodes it can make dirty")) {
                    // Db.checkDirtyNodes (bergdb 005-31): a documented refusal of a
                    // transaction whose index nodes may not fit one record.
                    holds = true;
                    result.refusedNodes++;
                } else {
                    holds = false;
                }
                if (!holds) {
                    fail(what + ": refused for a reason that does not hold (" + bytes
                            + " bytes, value limit " + valueLimit() + ", clock " + clockTime
                            + ", last user transaction " + lastUserTime + ")", e);
                }
                note("  refused: " + m);
                checkActive();
                for (Op op : ops) {
                    checkKey(op.key);
                }
                updateCuts();
                return false;
            }
            check(!clockOut, what + ": taken with the clock out of range, " + clockTime);
            check(ops.size() <= Db.MAX_OPERATIONS, what + ": taken with " + ops.size()
                    + " operations, over L1");
            check(!over, what + ": taken with " + bytes + " bytes, over the value limit "
                    + valueLimit());
            check(t.tt > lastUserTime, what + ": its time " + t.tt + " not after the last, "
                    + lastUserTime);
            check(t.tt <= Klong.MAX_TIME, what + ": taken at " + t.tt
                    + ", after the last time");
            lastUserTime = t.tt;
            check(!callers, what + ": a transformation's result above the value limit was "
                    + "taken (bergdb 026-06)");
            check(madeBytes(ops) <= valueLimit(), what + ": taken with " + madeBytes(ops)
                    + " bytes after its transformations, over the value limit " + valueLimit());
            for (Op op : ops) {
                ref.put(op.key, op.vt != null ? op.made : op.value);
            }
            result.committed++;
            checkActive();
            for (Op op : ops) {
                checkKey(op.key);
            }
            updateCuts();
            return true;
        }

        /** The value nodes of ops with the results of their transformations (026-06). */
        long madeBytes(List<Op> ops) {
            long n = 0;
            for (Op op : ops) {
                n += StoredValueNode.getByteSizeLong(op.vt != null && op.made != null ? op.made
                        : op.value, Keys.toSegments(op.key));
            }
            return n;
        }

        // ======== Values ========

        byte[] value(int length) {
            byte[] v = new byte[length];
            byte b = (byte) r.nextInt();
            Arrays.fill(v, b);
            for (int i = 0; i < Math.min(8, length); i++) {
                v[i] = (byte) r.nextInt();
            }
            if (length > 8) {
                v[length - 1] = (byte) r.nextInt();
            }
            return v;
        }

        /** The value length that makes key's value node take at most nodeBytes. */
        int lengthFor(String key, long nodeBytes) {
            long[] k = Keys.toSegments(key);
            long n = nodeBytes - 28 - 8L * k.length;
            while (n > 0 && StoredValueNode.getByteSizeLong(new byte[(int) n], k) > nodeBytes) {
                n--;
            }
            return (int) Math.max(0, n);
        }

        /** A small offset from the limit: 0, a few bytes, or more; below or above. */
        long edge() {
            switch (r.nextInt(8)) {
                case 0: return 0;
                case 1: return 1;
                case 2: return 3;
                case 3: return 4;
                case 4: return 5;
                case 5: return 100;
                case 6: return 1 + r.nextInt(5000);
                default: return 1 + r.nextInt((int) Math.min(100000, valueLimit() / 2));
            }
        }

        String smallKey() {
            return "/k/" + r.nextInt(60);
        }

        String bigKey() {
            return "/v/" + r.nextInt(16);
        }

        /**
         * A key of 24 to 111 bytes, the most (L2), and one in ten of 112, which the builder
         * refuses (bergdb 024-24; until then 24 to 3,010 bytes).
         */
        String longKey() {
            int[] lengths = {20, 50, 70, 100};
            int n = r.nextInt(10) == 0 ? Db.MAX_KEY_BYTES - 3
                    : r.nextInt(10) == 0 ? Db.MAX_KEY_BYTES - 4
                    : lengths[r.nextInt(lengths.length)] + r.nextInt(8);
            char[] c = new char[n];
            Arrays.fill(c, (char) ('a' + r.nextInt(3)));
            return "/l/" + r.nextInt(4) + new String(c);
        }

        // ======== The steps ========

        void putSmall() {
            List<Op> ops = new ArrayList<Op>();
            int n = 1 + r.nextInt(3);
            List<String> keys = new ArrayList<String>();
            for (int i = 0; i < n; i++) {
                String k = smallKey();
                if (!keys.contains(k)) {
                    keys.add(k);
                    ops.add(new Op(k, value(r.nextInt(100)), null));
                }
            }
            execute(ops, "put small", false);
        }

        /** One value whose node takes the value limit, or a few bytes less or more. */
        void putAtLimit() {
            String k = r.nextInt(5) == 0 ? longKey() : bigKey();
            boolean above = r.nextInt(4) == 0;
            long e = edge();
            long target = above ? valueLimit() + Math.max(1, e) : valueLimit() - e;
            int n = lengthFor(k, target);
            if (above) {
                while (StoredValueNode.getByteSizeLong(new byte[n], Keys.toSegments(k))
                        <= valueLimit()) {
                    n++;
                }
            }
            List<Op> ops = new ArrayList<Op>();
            ops.add(new Op(k, value(n), null));
            execute(ops, above ? "put above the limit" : "put at the limit", false);
        }

        /** Several values whose nodes take the value limit together, or a little more. */
        void putManyAtLimit() {
            int m = 2 + r.nextInt(5);
            boolean above = r.nextInt(4) == 0;
            long e = edge();
            long target = above ? valueLimit() + Math.max(1, e) : valueLimit() - e;
            List<Op> ops = new ArrayList<Op>();
            List<String> keys = new ArrayList<String>();
            while (keys.size() < m) {
                String k = r.nextBoolean() ? bigKey() : smallKey();
                if (!keys.contains(k)) {
                    keys.add(k);
                }
            }
            long left = target;
            for (int i = 0; i < m; i++) {
                String k = keys.get(i);
                long part = i == m - 1 ? left : left / (m - i) + r.nextInt(1000) - 500;
                part = Math.max(StoredValueNode.getByteSizeLong(new byte[0],
                        Keys.toSegments(k)), part);
                byte[] v = value(lengthFor(k, part));
                Op op = new Op(k, v, null);
                left -= op.nodeBytes();
                ops.add(op);
            }
            execute(ops, "put many at the limit", false);
        }

        void delete() {
            List<Op> ops = new ArrayList<Op>();
            String k = r.nextBoolean() ? bigKey() : smallKey();
            ops.add(new Op(k, null, null));
            if (r.nextBoolean()) {
                String k2 = smallKey();
                if (!k2.equals(k)) {
                    ops.add(new Op(k2, null, null));
                }
            }
            execute(ops, "delete", false);
        }

        /**
         * A put with a value transformation that grows the value: its result is a value of
         * the given length, made of its input and the previous value. Within the limit
         * (resultBytes: the result's node at most what is left of the value limit), or,
         * for the caller's fault, above it, which is refused (bergdb 026-06). With a second
         * KV, a result near the limit may take the transaction above it: refused too.
         */
        void transform(boolean callers) {
            String k = r.nextBoolean() ? bigKey() : smallKey();
            final byte[] in = value(r.nextInt(50));
            final long target;
            if (callers) {
                // Above the value limit: within the record limit or beyond it.
                target = r.nextBoolean() ? valueLimit() + 1 + r.nextInt(1000)
                        : recordLimit + 1 + r.nextInt(100000);
            } else {
                long e = edge();
                target = r.nextInt(3) == 0 ? valueLimit() - e : 100 + r.nextInt(5000);
            }
            final int length = lengthFor(k, target) + (callers ? 8 : 0);
            List<Op> ops = new ArrayList<Op>();
            final Op[] holder = new Op[1];
            ValueTransformation vt = new ValueTransformation() {
                public byte[] transform(long transTime, byte[] input, byte[] previous) {
                    byte[] out = new byte[length];
                    Arrays.fill(out, (byte) transTime);
                    System.arraycopy(input, 0, out, 0, Math.min(input.length, length));
                    if (previous != null && length > input.length) {
                        System.arraycopy(previous, 0, out, input.length,
                                Math.min(previous.length, Math.min(64, length - input.length)));
                    }
                    holder[0].made = out;
                    return out;
                }
            };
            Op op = new Op(k, in, vt);
            holder[0] = op;
            ops.add(op);
            if (!callers && r.nextBoolean()) {
                String k2 = smallKey();
                if (!k2.equals(k)) {
                    ops.add(new Op(k2, value(r.nextInt(30)), null));
                }
            }
            execute(ops, callers ? "transform above the limit (the caller's fault)"
                    : "transform", callers);
        }

        /**
         * Many small KVs in one transaction, at the bound of its index nodes, and around L1:
         * those of more than 500 KVs are refused (bergdb 024-24).
         */
        void putManyKeys() {
            List<Op> ops = new ArrayList<Op>();
            int n = r.nextInt(3) == 0 ? Db.MAX_OPERATIONS + r.nextInt(2) : 50 + r.nextInt(1500);
            java.util.HashSet<String> keys = new java.util.HashSet<String>();
            while (ops.size() < n) {            // n distinct keys (bergdb 024-24)
                String k = "/m/" + r.nextInt(5000);
                if (keys.add(k)) {
                    ops.add(new Op(k, value(r.nextInt(20)), null));
                }
            }
            execute(ops, "put many keys", false);
        }

        void putLongKey() {
            List<Op> ops = new ArrayList<Op>();
            int n = 1 + (r.nextInt(4) == 0 ? r.nextInt(6) : 0);
            List<String> keys = new ArrayList<String>();
            for (int i = 0; i < n; i++) {
                String k = longKey();
                if (!keys.contains(k)) {
                    keys.add(k);
                    ops.add(new Op(k, value(r.nextInt(200)), null));
                }
            }
            execute(ops, "put long keys", false);
        }

        /** The clock goes back, or out of the range for one transaction. */
        void clockEdge() {
            switch (r.nextInt(4)) {
                case 0: {
                    long back = 1 + (long) r.nextInt((int) Clock.UNITS_PER_SEC);
                    now.set(Math.max(0, now.get() - back));
                    maxClock = Math.max(maxClock, now.get());
                    note("clock back to " + now.get());
                    putSmall();
                    break;
                }
                default: {
                    long saved = now.get();
                    long[] outside = {-1, Long.MIN_VALUE, Klong.MAX_TIME + 1,
                            Klong.MAX_TIME + 1 + r.nextInt(1000), Long.MAX_VALUE};
                    now.set(outside[r.nextInt(outside.length)]);
                    try {
                        putSmall();
                    } finally {
                        now.set(saved);
                    }
                }
            }
        }

        void setting() {
            result.settings++;
            switch (r.nextInt(4)) {
                case 0: setStartupDistance(); break;
                case 1: setRetainDuration(); break;
                case 2: setFraction(); break;
                default: setCacheSize();
            }
            checkActive();
            updateCuts();
        }

        /**
         * Db.setStartupDistance's Javadoc (bergdb 015-76, 028-13): the value is clamped to 10
         * to 10^9, the clamped value is set and returned; a call whose clamped value is in
         * force writes nothing, others write; a value below 1 is refused and changes nothing.
         */
        void setStartupDistance() {
            int v = SD_ARGS[r.nextInt(SD_ARGS.length)];
            if (r.nextInt(4) == 0) {
                v = startupDistance;
            }
            int clamped = Math.max(10, Math.min(1000 * 1000 * 1000, v));
            long length = db.getStreamLength();
            note("setStartupDistance(" + v + "), in force " + startupDistance);
            int returned = -1;
            try {
                returned = db.setStartupDistance(v);
            } catch (IllegalArgumentException e) {
                check(v < 1, "setStartupDistance(" + v + ") refused: " + e);
                check(db.getStartupDistance() == startupDistance, "a refused "
                        + "setStartupDistance changed the setting");
                return;
            } catch (DbFailedException e) {
                fail("setStartupDistance(" + v + "): the database failed", e.getCause());
            } catch (DbException e) {
                String m = String.valueOf(e.getMessage());
                check(refusedAtEnd(m), "setStartupDistance(" + v + ") refused: " + m);
                check(db.getStartupDistance() == startupDistance, "a refused "
                        + "setStartupDistance changed the setting");
                result.refusedTime++;
                return;
            }
            check(v >= 1, "setStartupDistance(" + v + ") was not refused");
            check(returned == clamped, "setStartupDistance(" + v + ") returned " + returned);
            check(db.getStartupDistance() == clamped, "setStartupDistance(" + v
                    + "): expected the setting " + clamped + ", got " + db.getStartupDistance());
            long after = db.getStreamLength();
            if (clamped == startupDistance) {
                check(after == length, "setStartupDistance(" + v + ") with " + clamped
                        + " in force wrote " + (after - length) + " bytes");
            } else {
                check(after > length, "setStartupDistance(" + v + ") from " + startupDistance
                        + " wrote nothing");
            }
            startupDistance = clamped;
        }

        void setRetainDuration() {
            long v = RETAIN_ARGS[r.nextInt(RETAIN_ARGS.length)];
            note("setRetainDuration(" + v + ")");
            try {
                db.setRetainDuration(v);
            } catch (IllegalArgumentException e) {
                check(v < Clock.UNITS_PER_SEC, "setRetainDuration(" + v + ") refused: " + e);
                check(db.getRetainDuration() == retain, "a refused setRetainDuration changed "
                        + "the setting");
                return;
            } catch (DbFailedException e) {
                fail("setRetainDuration(" + v + "): the database failed", e.getCause());
            } catch (DbException e) {
                String m = String.valueOf(e.getMessage());
                check(refusedAtEnd(m), "setRetainDuration(" + v + ") refused: " + m);
                check(db.getRetainDuration() == retain, "a refused setRetainDuration changed "
                        + "the setting");
                result.refusedTime++;
                return;
            }
            check(v >= Clock.UNITS_PER_SEC, "setRetainDuration(" + v + ") was not refused");
            check(db.getRetainDuration() == v, "setRetainDuration(" + v + "): got "
                    + db.getRetainDuration());
            retain = v;
        }

        void setFraction() {
            double v = FRACTION_ARGS[r.nextInt(FRACTION_ARGS.length)];
            boolean valid = !Double.isNaN(v) && v >= 0.001 && v <= 0.90;
            note("setReclaimInternalFraction(" + v + ")");
            try {
                db.setReclaimInternalFraction(v);
            } catch (IllegalArgumentException e) {
                check(!valid, "setReclaimInternalFraction(" + v + ") refused: " + e);
                return;
            } catch (DbFailedException e) {
                fail("setReclaimInternalFraction(" + v + "): the database failed", e.getCause());
            } catch (DbException e) {
                String m = String.valueOf(e.getMessage());
                check(refusedAtEnd(m), "setReclaimInternalFraction(" + v + ") refused: " + m);
                result.refusedTime++;
                return;
            }
            check(valid, "setReclaimInternalFraction(" + v + ") was not refused");
            int units = (int) Math.round(v * Reclaim.FRACTION_ONE);
            check(db.internal().reclaim().getInternalFractionUnits() == units,
                    "setReclaimInternalFraction(" + v + "): expected " + units + " units, got "
                    + db.internal().reclaim().getInternalFractionUnits());
            fractionUnits = units;
        }

        void setCacheSize() {
            long v = CACHE_ARGS[r.nextInt(CACHE_ARGS.length)];
            note("setCacheSizeIndicator(" + v + ")");
            try {
                db.setCacheSizeIndicator(v);
            } catch (IllegalArgumentException e) {
                check(v < 1, "setCacheSizeIndicator(" + v + ") refused: " + e);
                check(db.getCacheSizeIndicator() == cacheIndicator, "a refused "
                        + "setCacheSizeIndicator changed the setting");
                return;
            }
            check(v >= 1, "setCacheSizeIndicator(" + v + ") was not refused");
            check(db.getCacheSizeIndicator() == v, "setCacheSizeIndicator(" + v + "): got "
                    + db.getCacheSizeIndicator());
            cacheIndicator = v;
        }

        /**
         * The clock goes to the last times, and stays there (bergdb 015-55; since 031-06, Q4,
         * the last is Klong.MAX_TIME for every transaction).
         */
        void enterEndPhase() {
            endPhase = true;
            long[] at = {Klong.MAX_TIME - r.nextInt(2000), Klong.MAX_TIME - 2,
                    Klong.MAX_TIME - 1, Klong.MAX_TIME - r.nextInt(5), Klong.MAX_TIME};
            now.set(at[r.nextInt(at.length)]);
            maxClock = Math.max(maxClock, now.get());
            note("the end phase: clock " + now.get());
        }

        boolean step() {
            if (step == endPhaseAt) {
                enterEndPhase();
            }
            if (endPhase) {
                long t = now.get() + r.nextInt(3);
                now.set(Math.min(t, Klong.MAX_TIME));
            } else {
                now.addAndGet(Clock.UNITS_PER_SEC / 40 + r.nextInt((int) Clock.UNITS_PER_SEC
                        / 20));
            }
            maxClock = Math.max(maxClock, now.get());
            if (step == faultAt) {
                transform(true);
                return true;
            }
            int x = r.nextInt(100);
            if (x < 35) {
                putSmall();
            } else if (x < 47) {
                putAtLimit();
            } else if (x < 54) {
                putManyAtLimit();
            } else if (x < 61) {
                delete();
            } else if (x < 70) {
                transform(false);
            } else if (x < 75) {
                if (r.nextInt(3) == 0) {
                    putManyKeys();
                } else {
                    putLongKey();
                }
            } else if (x < 79) {
                clockEdge();
            } else if (x < 86) {
                setting();
            } else if (x < 88) {
                restart();
            } else {
                putSmall();
                if (!ref.isEmpty()) {
                    String k = ref.keySet().toArray(new String[0])[r.nextInt(ref.size())];
                    checkKey(k);
                }
            }
            return true;
        }
    }

    /** One run of steps from a seed; throws AssertionError at a failure. */
    public static Result run(long seed, int steps) {
        Run run = new Run(seed, steps);
        final long saved = StoredTrans.recordLimit;
        StoredTrans.recordLimit = run.recordLimit;
        try {
            run.startFirst();
            for (run.step = 0; run.step < steps; run.step++) {
                if (!run.step()) {
                    break;
                }
            }
            run.step = steps;
            run.checkAll();
            run.restart();
            List<Run.Op> one = new ArrayList<Run.Op>();
            one.add(run.new Op("/k/last", new byte[] {7}, null));
            run.execute(one, "put after the last restart", false);
            run.result.iterations += run.db == null ? 0 : run.db.getReclaimIterationCount();
            return run.result;
        } finally {
            try {
                run.stop();
            } finally {
                StoredTrans.recordLimit = saved;
            }
        }
    }

    static String show(byte[] b) {
        if (b == null) {
            return "null";
        }
        if (b.length <= 4) {
            return Arrays.toString(b);
        }
        return "[" + b.length + " bytes: " + b[0] + ", " + b[1] + ", ..., " + b[b.length - 1]
                + "]";
    }

    // ======== Tests ========

    /** Short runs on fixed seeds: the unit tests. */
    @Nano
    public static void testSeeds() {
        for (long seed = 1; seed <= 3; seed++) {
            run(seed, 100);
        }
    }

    /**
     * Longer runs for the night tests: 20 seeds of 500 steps, new seeds each day (the
     * day's number times 1000), printed, so that a failure can be repeated with
     * main(seed, 500).
     */
    @Nano("night")
    public static void testSeedsLong(TestEnvironment c) {
        long base = System.currentTimeMillis() / 86400000L * 1000;
        c.out().println("LimitsTester: seeds " + base + " to " + (base + 19)
                + ", 500 steps each");
        Result total = new Result();
        for (long seed = base; seed < base + 20; seed++) {
            Result res = run(seed, 500);
            total.add(res);
        }
        c.out().println("LimitsTester: " + total);
    }

    /** Usage: LimitsTester [SEED [STEPS [RUNS]]]. */
    public static void main(String[] args) {
        long seed = args.length > 0 ? Long.parseLong(args[0]) : System.nanoTime();
        int steps = args.length > 1 ? Integer.parseInt(args[1]) : 1000;
        int runs = args.length > 2 ? Integer.parseInt(args[2]) : 1;
        boolean verbose = Boolean.getBoolean("bergdb.limits.verbose");
        Result total = new Result();
        for (int i = 0; i < runs; i++) {
            Result res = run(seed + i, steps);
            total.add(res);
            if (verbose) {
                System.out.println("LimitsTester: seed " + (seed + i) + ": " + res);
            }
        }
        System.out.println("LimitsTester: seeds " + seed + " to " + (seed + runs - 1) + ", "
                + steps + " steps: " + total);
        System.out.println("LimitsTester OK");
    }
}
