package bergdb.core;

import java.io.IOException;
import java.util.concurrent.atomic.AtomicReference;

import bergdb.common.StringUtil;
import bergdb.dag.Keys;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.util.Clock;
import bergdb.pub.util.IllegalDbStateException;
import bergdb.storage.RecoverableStream;
import bergdb.stream.CutStream;

/**
 * Tests of Db.maintain(budget) (bergdb 024-32, 031-04): a call's work is bounded by its
 * budget, a call when nothing is due writes nothing, an emptied database that is not
 * written to comes back to about a fresh one's stream by maintain() calls alone, also when
 * emptied again after a cut, one written slowly keeps little, and one with live values
 * that is not written to is quiet (028-51), reads are right during and after, and the
 * stream follows the calls, also over a restart (010-01, P2).
 */
public class ReclaimMaintainTester {
    private static final long SEC = Clock.UNITS_PER_SEC;
    private static final long MS = SEC / 1000;
    private static final byte[] HELLO = StringUtil.toBytes("Hello world!");
    
    /** The budget of a call in these tests: the least, about 100 kB written. */
    private static final int BUDGET = Reclaim.MAINTAIN_MIN_BUDGET;
    
    /**
     * What an emptied database may keep beyond twice a fresh one's stream: 600 kB, as
     * 024-32's G5 allows (java/stress/CountGates.java).
     */
    private static final long ALLOWANCE = 3L * RecoverableStream.META_BLOCK_DISTANCE;

    private ReclaimMaintainTester() {}

    /** A database on a CutStream (reads below the cut are refused) and a test clock. */
    private static final class Run {
        CutStream stream = new CutStream();
        final CoreTestClock clock = new CoreTestClock();
        final int startupDistance;
        long time = SEC;
        Db db;
        Reclaim.Stats stats;
        long liveTime;      // The time of the live keys' put, after it "/a.txt" and they hold.

        Run(long retain) {
            this(retain, 100000);
        }

        Run(long retain, int startupDistance) {
            this.startupDistance = startupDistance;
            clock.setTime(time);
            start();
            if (retain != Long.MAX_VALUE) {
                db.setRetainDuration(retain);
            }
            exec(db.trans().put("/a.txt", HELLO));
        }

        void start() {
            db = Db.builder().testSetup(stream).clock(clock).start();
            db.setStartupDistance(startupDistance);
            synchronized (db.internal().getWriteLock()) {
                stats = db.internal().reclaim().enableStats();
            }
        }

        void tick() {
            advance(MS);
        }

        void advance(long dt) {
            time += dt;
            clock.setTime(time);
        }

        /** Calls maintain() with the largest budget. */
        void maintainUntilFalse() {
            db.maintain(Reclaim.MAINTAIN_MAX_BUDGET);
        }
        
        /** Calls maintain(BUDGET); returns whether it wrote. */
        boolean maintain() {
            final long length = db.getStreamLength();
            db.maintain(BUDGET);
            return db.getStreamLength() != length;
        }

        void exec(Trans.Builder b) {
            tick();
            db.execute(b.build());
        }

        /** Puts n keys "/k/i" of 100 bytes, 100 a transaction, and 'live' keys "/live/i". */
        void fill(int n, int live) {
            for (int i = 0; i < n; i += 100) {
                Trans.Builder b = db.trans();
                for (int j = i; j < i + 100 && j < n; j++) b.put("/k/" + j, new byte[100]);
                exec(b);
            }
            Trans.Builder b = db.trans();
            for (int j = 0; j < live; j++) b.put("/live/" + j, "v" + j);
            exec(b);
            liveTime = db.currentTime();
        }

        void deleteAll(int n) {
            for (int i = 0; i < n; i += 100) {
                Trans.Builder b = db.trans();
                for (int j = i; j < i + 100 && j < n; j++) b.delete("/k/" + j);
                exec(b);
            }
        }

        long records() {
            return stats.user.records + stats.step.records + stats.table.records;
        }

        long kept() {
            return db.getStreamLength() - db.getFirstAvailablePos();
        }

        byte[] get(long time, String key) {
            return db.getOne(time, Keys.toSegments(key), db.newGetData());
        }

        void restart() {
            db.close();
            stream = stream.copy();
            start();
        }

        /** The stream's bytes from its first position to its end. */
        byte[] bytes() throws IOException {
            long first = stream.getFirstPos();
            byte[] b = new byte[(int) (stream.getLength() - first)];
            stream.read(first, b, 0, b.length);
            return b;
        }
    }

    /**
     * With the retain duration forever nothing is due; on a fresh database with a finite one,
     * one pass and its cut, then nothing (bergdb 031-04).
     */
    @Nano
    public static void testNothingDue() {
        for (long retain : new long[] {Long.MAX_VALUE, SEC}) {
            Run r = new Run(retain);
            try {
                r.fill(1000, 0);
                long length = r.db.getStreamLength();
                for (int i = 0; i < 3000; i++) {
                    r.tick();
                    final boolean wrote = r.maintain();
                    Assert.assertFalse("retain " + retain + ", call " + i,
                            wrote && (retain == Long.MAX_VALUE || i >= 1500));
                    if (i == 1500) {
                        length = r.db.getStreamLength();
                    }
                }
                Assert.assertEquals("nothing written, retain " + retain, length,
                        r.db.getStreamLength());
            } finally {
                r.db.close();
            }
        }
    }

    /** maintain() on a stopped database throws as a transaction does. */
    @Nano
    public static void testStopped() {
        Run r = new Run(SEC);
        r.db.close();
        try {
            r.db.maintain(BUDGET);
            throw new AssertionError("maintain() after close()");
        } catch (IllegalDbStateException e) {
            // expected
        }
    }

    /**
     * An emptied database, not written to after its deletes, comes back to about a fresh
     * hello-world database's stream by maintain() calls alone, one a millisecond of the
     * test clock (023-03, T1's second drive): each call's work is bounded by its budget, the
     * calls write nothing once it has converged, and reads are right throughout, also in a
     * thread of their own.
     */
    @Nano
    public static void testEmptiedDatabaseConverges() throws Exception {
        final int n = 20000, live = 50;
        Run twin = new Run(SEC);
        Run r = new Run(SEC);
        try {
            r.fill(n, live);
            r.deleteAll(n);
            twin.fill(0, live);
            final long keptBefore = r.kept();

            final AtomicReference<Throwable> failure = new AtomicReference<Throwable>();
            final Db db = r.db;
            final boolean[] stop = new boolean[1];
            Thread reader = new Thread(() -> {
                try {
                    for (int k = 0; !stopped(stop); k++) {
                        String key = "/live/" + (k % live);
                        byte[] v = db.getOne(Long.MAX_VALUE, Keys.toSegments(key),
                                db.newGetData());
                        Assert.assertEquals(key, "v" + (k % live), StringUtil.toString(v));
                    }
                } catch (Throwable e) {
                    failure.set(e);
                }
            });
            reader.start();

            long maxGrowth = 0, maxRecords = 0, lastTrue = -1, lengthAtLastTrue = -1;
            final int calls = 20000;      // 20 R
            for (int i = 0; i < calls; i++) {
                r.tick();
                twin.tick();
                final long length = r.db.getStreamLength(), records = r.records();
                r.db.maintain(BUDGET);
                twin.db.maintain(BUDGET);
                maxGrowth = Math.max(maxGrowth, r.db.getStreamLength() - length);
                maxRecords = Math.max(maxRecords, r.records() - records);
                if (r.db.getStreamLength() != length) {
                    lastTrue = i;
                    lengthAtLastTrue = r.db.getStreamLength();
                }
                if (i % 97 == 0) {
                    checkReads(r, live, n);
                }
            }
            synchronized (stop) {
                stop[0] = true;
            }
            reader.join(60_000);
            Assert.assertFalse("the reader thread did not end within 60 s", reader.isAlive());
            if (failure.get() != null) throw new AssertionError("the reader", failure.get());
            checkReads(r, live, n);

            // Bounded work: a call writes about its budget, and at most one part more: a
            // filler, a take, a step.
            Assert.assertTrue("growth of a call " + maxGrowth, maxGrowth
                    < BUDGET * Reclaim.MAINTAIN_UNIT + RecoverableStream.META_BLOCK_DISTANCE
                    + Reclaim.MAINTAIN_TAKE_BYTES + 100000);
            Assert.assertTrue("records of a call " + maxRecords, maxRecords <= 100);
            // Converged, and quiet: the last 5 R wrote nothing.
            Assert.assertTrue("last call with work " + lastTrue, lastTrue < calls - 5000);
            Assert.assertEquals(lengthAtLastTrue, r.db.getStreamLength());
            Assert.assertFalse(r.maintain());
            // About a fresh database's stream: within twice the twin's and 600 kB.
            final long allowance = ALLOWANCE;
            Assert.assertTrue("kept " + r.kept() + " (before " + keptBefore + "), the twin's "
                    + twin.kept(), r.kept() <= 2 * twin.kept() + allowance);
            Assert.assertTrue("kept before " + keptBefore, keptBefore > 4 * allowance);

            // And after a restart.
            r.restart();
            checkReads(r, live, n);
            Assert.assertFalse(r.maintain());
        } finally {
            r.db.close();
            twin.db.close();
        }
    }

    /**
     * An emptied database that maintain() has brought back, then filled and emptied again,
     * is brought back again by maintain() calls alone (bergdb 028-51). Its first cut is that
     * of the first iteration, which cuts at its own pStart: until 028-51, M1 began an
     * iteration only if its own cut released 400 kB, and with a startup distance above half
     * the second filling's stream, so that no commit began one, that stream stayed for good.
     * Since 031-04 every pass that a call begins cuts at its own pStart.
     */
    @Nano
    public static void testEmptiedAgainAfterACut() {
        final int n = 20000, sd = 5000000;
        Run twin = new Run(SEC, sd);
        Run r = new Run(SEC, sd);
        try {
            for (Run x : new Run[] {r, twin}) {
                x.fill(4000, 0);
                x.deleteAll(4000);
                for (int i = 0; i < 3000 && x.db.getFirstAvailablePos() == 0; i++) {
                    x.tick();
                    x.maintainUntilFalse();
                }
                Assert.assertTrue("the first cut", x.db.getFirstAvailablePos() > 0);
            }
            r.fill(n, 0);
            r.deleteAll(n);
            final long keptBefore = r.kept();

            long lastWork = -1;
            final int calls = 10000;      // 10 R
            for (int i = 0; i < calls; i++) {
                r.tick();
                twin.tick();
                final long length = r.db.getStreamLength();
                r.db.maintain(BUDGET);
                twin.db.maintain(BUDGET);
                if (r.db.getStreamLength() != length) {
                    lastWork = i;
                }
            }
            final long allowance = ALLOWANCE;
            Assert.assertTrue("kept before " + keptBefore, keptBefore > 4 * allowance);
            Assert.assertTrue("kept " + r.kept() + " (before " + keptBefore + "), the twin's "
                    + twin.kept(), r.kept() <= 2 * twin.kept() + allowance);
            Assert.assertTrue("last call with work " + lastWork, lastWork < calls - 3000);
            Assert.assertFalse(r.maintain());
        } finally {
            r.db.close();
            twin.db.close();
        }
    }

    /**
     * A database written slowly, with maintain() of the largest budget after each commit, keeps about
     * the stream of a few retain durations, not twice its startup distance (bergdb 028-51;
     * 028-47, finding F1): a value of 10 kB every 10 ms, 1 MB a retain duration R, so that
     * R/4 writes less than the 400 kB that M1 asks a cut to release, and a startup distance
     * of 5 MB, so that no commit begins an iteration before 10 MB of growth. Until 028-51,
     * once the first iteration (or one that began R/4 after an iteration with nothing to
     * cut) was cut, M1 began no iteration, and the stream kept grew to about 10 MB.
     */
    @Nano
    public static void testSlowlyWritten() {
        final int sd = 5000000, perR = 100, rs = 30;
        Run r = new Run(SEC, sd);
        try {
            final byte[] v = new byte[10000];
            long maxKept = 0;
            for (int i = 1; i <= rs * perR; i++) {
                v[0] = (byte) i;
                v[1] = (byte) (i >> 8);
                r.advance(SEC / perR - MS);
                r.exec(r.db.trans().put("/w", v));
                r.maintainUntilFalse();
                if (r.db.getFirstAvailablePos() > 0) {
                    maxKept = Math.max(maxKept, r.kept());
                }
            }
            Assert.assertTrue("a cut", r.db.getFirstAvailablePos() > 0);
            // At most the writes of 4 R and the allowance of testEmptiedDatabaseConverges:
            // 3.5 MB measured (028-51), 12.1 MB before 028-51.
            Assert.assertTrue("kept " + maxKept, maxKept < 4 * perR * v.length + ALLOWANCE);
        } finally {
            r.db.close();
        }
    }

    /**
     * A database with live values, not written to, is quiet after the first iteration's
     * cut (bergdb 028-51): the stream since that iteration began holds its rewrites of every
     * live value, and a rule that counted it would begin iterations that rewrite them
     * again and again, about an R apart, to release only their own copies. Since 031-04 a
     * call begins a pass only while the stream kept holds a record of the application's.
     */
    @Nano
    public static void testLiveDatabaseQuiet() {
        Run r = new Run(SEC, 5000000);
        try {
            r.fill(5000, 0);                // 5,000 live values, about 700 kB of stream
            final int calls = 10000;        // 10 R
            long lengthAtHalf = -1;
            for (int i = 0; i < calls; i++) {
                r.tick();
                r.maintainUntilFalse();
                if (i == calls / 2) {
                    lengthAtHalf = r.db.getStreamLength();
                }
            }
            Assert.assertTrue("the first cut", r.db.getFirstAvailablePos() > 0);
            Assert.assertEquals("written in the last 5 R", lengthAtHalf,
                    r.db.getStreamLength());
            Assert.assertFalse(r.maintain());
        } finally {
            r.db.close();
        }
    }

    /**
     * The handover of the write lock (bergdb 031-04, Q9): a commit that waits for the lock
     * goes before the next part of maintain() calls that wait with it, here two calls at
     * once. The test holds the lock, starts the commit, waits until it counts as waiting
     * (writersWaiting), starts the calls, waits until both are parked in the handover, and
     * lets the lock go: the first record after that is the commit's, and the calls then
     * write their parts. writersWaiting is 0 at the end.
     */
    @Nano
    public static void testCommitGoesBeforeTheNextPart() throws Exception {
        Run r = new Run(SEC);
        try {
            r.fill(5000, 0);
            r.advance(2 * SEC);         // past R: a call begins a pass, and writes
            final Db db = r.db;
            final AtomicReference<Throwable> failure = new AtomicReference<Throwable>();
            final Thread w = new Thread(() -> {
                try {
                    db.execute(db.trans().put("/w", "w").build());
                } catch (Throwable e) {
                    failure.set(e);
                }
            });
            final Thread[] m = new Thread[2];
            for (int i = 0; i < m.length; i++) {
                m[i] = new Thread(() -> {
                    try {
                        db.maintain(Reclaim.MAINTAIN_MAX_BUDGET);
                    } catch (Throwable e) {
                        failure.set(e);
                    }
                });
            }
            final long released;
            synchronized (db.internal().getWriteLock()) {
                w.start();
                final long end = System.nanoTime() + 10_000_000_000L;
                while (db.internal().writersWaiting() == 0 && System.nanoTime() < end) {
                    Thread.sleep(1);
                }
                Assert.assertEquals("the commit waits", 1, db.internal().writersWaiting());
                for (Thread t : m) t.start();
                for (Thread t : m) {
                    while (t.getState() != Thread.State.TIMED_WAITING
                            && System.nanoTime() < end) {
                        Thread.sleep(1);
                    }
                    Assert.assertEquals("the call gives way", Thread.State.TIMED_WAITING,
                            t.getState());
                }
                released = db.getStreamLength();
            }
            w.join(10_000);
            for (Thread t : m) t.join(60_000);
            if (failure.get() != null) throw new AssertionError("failed", failure.get());
            Assert.assertFalse("the threads ended", w.isAlive() || m[0].isAlive()
                    || m[1].isAlive());
            Assert.assertTrue("the calls wrote", db.getStreamLength() > released);
            Assert.assertEquals("no writer waits", 0, db.internal().writersWaiting());
            synchronized (db.internal().getWriteLock()) {
                NodeStream.TransIterator ti =
                        db.internal().nodeStream().createTransIteratorFromExactStartupPos(released);
                Assert.assertTrue(ti.next());
                Assert.assertTrue("the first record is the commit's",
                        r.get(ti.transTime, "/w") != null);
                Assert.assertNull(r.get(ti.transTime - 1, "/w"));
            }
        } finally {
            r.db.close();
        }
    }

    private static boolean stopped(boolean[] stop) {
        synchronized (stop) {
            return stop[0];
        }
    }

    /** The live keys and "/a.txt" at the latest time and at the first available time. */
    private static void checkReads(Run r, int live, int n) {
        final long first = Math.max(r.liveTime, r.db.getFirstAvailableLookupTime());
        for (long t : new long[] {Long.MAX_VALUE, first}) {
            Assert.assertEquals("Hello world!", StringUtil.toString(r.get(t, "/a.txt")));
            for (int j = 0; j < live; j += 7) {
                Assert.assertEquals("v" + j, StringUtil.toString(r.get(t, "/live/" + j)));
            }
        }
        Assert.assertNull(r.get(Long.MAX_VALUE, "/k/" + (n / 2)));
    }

    /**
     * The stream follows the calls (010-01, P2): the same calls, with a restart among them,
     * give the same stream, byte for byte, and the same cut.
     */
    @Nano
    public static void testSameStreamOverARestart() throws IOException {
        final int n = 10000;
        Run a = new Run(SEC), b = new Run(SEC);
        try {
            for (Run r : new Run[] {a, b}) {
                r.fill(n, 10);
                r.deleteAll(n);
            }
            for (int i = 0; i < 6000; i++) {
                if (i == 1500 || i == 3100) {
                    b.restart();
                }
                a.tick();
                b.tick();
                a.db.maintain(BUDGET);
                b.db.maintain(BUDGET);
                Assert.assertEquals("call " + i, a.db.getStreamLength(),
                        b.db.getStreamLength());
            }
            Assert.assertTrue("cut", a.db.getFirstAvailablePos() > 0);
            Assert.assertEquals(a.db.getFirstAvailablePos(), b.db.getFirstAvailablePos());
            Assert.assertEquals(a.db.getStreamLength(), b.db.getStreamLength());
            Assert.assertTrue("the same bytes",
                    java.util.Arrays.equals(a.bytes(), b.bytes()));
        } finally {
            a.db.close();
            b.db.close();
        }
    }
}
