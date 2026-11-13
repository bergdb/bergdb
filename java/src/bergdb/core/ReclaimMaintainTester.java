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
 * Tests of Db.maintain() (bergdb 024-32): a call's work is bounded, a call when nothing is
 * due writes nothing and returns false, an emptied database that is not written to comes
 * back to about a fresh one's stream by maintain() calls alone, reads are right during and
 * after, and the stream follows the calls, also over a restart (010-01, P2).
 */
public class ReclaimMaintainTester {
    private static final long SEC = Clock.UNITS_PER_SEC;
    private static final long MS = SEC / 1000;
    private static final byte[] HELLO = StringUtil.toBytes("Hello world!");

    private ReclaimMaintainTester() {}

    /** A database on a CutStream (reads below the cut are refused) and a test clock. */
    private static final class Run {
        CutStream stream = new CutStream();
        final CoreTestClock clock = new CoreTestClock();
        long time = SEC;
        Db db;
        Reclaim.Stats stats;
        long liveTime;      // The time of the live keys' put, after it "/a.txt" and they hold.

        Run(long retain) {
            clock.setTime(time);
            start();
            if (retain != Long.MAX_VALUE) {
                db.setRetainDuration(retain);
            }
            exec(db.trans().put("/a.txt", HELLO));
        }

        void start() {
            db = Db.builder().testSetup(stream).clock(clock).startupDistance(100000).start();
            synchronized (db.internal().getWriteLock()) {
                stats = db.internal().reclaim().enableStats();
            }
        }

        void tick() {
            time += MS;
            clock.setTime(time);
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

    /** With the retain duration forever, and on a fresh database, nothing is due. */
    @Nano
    public static void testNothingDue() {
        for (long retain : new long[] {Long.MAX_VALUE, SEC}) {
            Run r = new Run(retain);
            try {
                r.fill(1000, 0);
                long length = r.db.getStreamLength();
                for (int i = 0; i < 3000; i++) {
                    r.tick();
                    Assert.assertFalse("retain " + retain + ", call " + i, r.db.maintain());
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
            r.db.maintain();
            throw new AssertionError("maintain() after close()");
        } catch (IllegalDbStateException e) {
            // expected
        }
    }

    /**
     * An emptied database, not written to after its deletes, comes back to about a fresh
     * hello-world database's stream by maintain() calls alone, one a millisecond of the
     * test clock (023-03, T1's second drive): each call's work is bounded, the calls return
     * false once it has converged and then write nothing, and reads are right throughout,
     * also in a thread of their own.
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
                final boolean more = r.db.maintain();
                twin.db.maintain();
                maxGrowth = Math.max(maxGrowth, r.db.getStreamLength() - length);
                maxRecords = Math.max(maxRecords, r.records() - records);
                if (more || r.db.getStreamLength() != length) {
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

            // Bounded work: a call writes at most a filler, a take and a few small records.
            Assert.assertTrue("growth of a call " + maxGrowth, maxGrowth
                    < RecoverableStream.META_BLOCK_DISTANCE + Reclaim.MAINTAIN_TAKE_BYTES
                    + 100000);
            Assert.assertTrue("records of a call " + maxRecords, maxRecords <= 10);
            // Converged, and quiet: the last 5 R wrote nothing and returned false.
            Assert.assertTrue("last call with work " + lastTrue, lastTrue < calls - 5000);
            Assert.assertEquals(lengthAtLastTrue, r.db.getStreamLength());
            Assert.assertFalse(r.db.maintain());
            // About a fresh database's stream: within twice the twin's and the bound that
            // the release threshold and a filler leave (bergdb 024-32, section 2.2).
            final long allowance = Reclaim.MAINTAIN_MIN_RELEASE
                    + RecoverableStream.META_BLOCK_DISTANCE;
            Assert.assertTrue("kept " + r.kept() + " (before " + keptBefore + "), the twin's "
                    + twin.kept(), r.kept() <= 2 * twin.kept() + allowance);
            Assert.assertTrue("kept before " + keptBefore, keptBefore > 4 * allowance);

            // And after a restart.
            r.restart();
            checkReads(r, live, n);
            Assert.assertFalse(r.db.maintain());
        } finally {
            r.db.close();
            twin.db.close();
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
                Assert.assertEquals("call " + i, a.db.maintain(), b.db.maintain());
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
