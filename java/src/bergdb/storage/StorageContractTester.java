package bergdb.storage;

import java.io.IOException;
import java.util.Random;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicReference;

import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.MemoryStream;
import bergdb.stream.ReadBelowFirstPosException;
import bergdb.stream.StreamContract;
import bergdb.stream.StrictStream;

/**
 * The stream contract (2026-11-05, bergdb 018-02) on BufferedStream and StorageManager: the
 * checks of StreamContract, on a MemoryStream; and the two on a StrictStream, which checks
 * every call that they make to the stream below: one writer, with R5-F5's forced order
 * (bergdb 015-80), and a short workload of appends, reads, cuts and syncs.
 */
public class StorageContractTester {

    private static final String BUFFERED = "BufferedStream";
    private static final String MANAGER = "StorageManager";

    /** A BufferedStream, started, or a StorageManager, started, on 'stream'. */
    private static AppendOnlyStream create(String impl, AppendOnlyStream stream, int bufferSize,
            int bufferTime) {
        if (impl.equals(BUFFERED)) {
            BufferedStream b = new BufferedStream(stream, bufferSize, bufferTime);
            b.start();
            return b;
        }
        StorageManager m = new StorageManager.Builder().stream(stream, bufferSize, bufferTime)
                .build();
        m.start();
        return m;
    }

    private static void check(TestEnvironment c, final String impl) {
        StreamContract.Results results = new StreamContract.Results();
        StreamContract.check(new StreamContract.Impl(impl,
                () -> create(impl, new MemoryStream(), 10 * 1000, 10))
                .cutBeyond(StreamContract.CutBeyond.HELD), results);
        results.assertOk(c.out());
    }

    @Nano
    public static void testBufferedStream(TestEnvironment c) {
        check(c, BUFFERED);
    }

    @Nano
    public static void testStorageManager(TestEnvironment c) {
        check(c, MANAGER);
    }

    // ======== One writer ========

    /**
     * R5-F5's forced order (bergdb 015-80, review R5): the thread of the buffer appends to the
     * stream below, held there by the hook, and the writer, with the write lock, cuts below
     * what has been flushed, and asks for the first position. Each must wait for the append or
     * go to that thread, not call the stream below beside it. The writer's calls run in a
     * thread of their own: a fix that makes them wait for the append is not taken for a
     * deadlock.
     */
    private static void oneWriter(TestEnvironment c, String impl) throws Exception {
        StreamContract.Results results = new StreamContract.Results();
        oneWriter(results, impl, "a cut during a flush", s -> s.pretruncate(50));
        oneWriter(results, impl, "getFirstPos() during a flush", s -> s.getFirstPos());
        results.assertOk(c.out());
    }

    interface WriterCall {
        void run(AppendOnlyStream s) throws IOException;
    }

    private static void oneWriter(StreamContract.Results results, String impl, String name,
            final WriterCall call) throws Exception {
        final Object writeLock = new Object();
        MemoryStream below = new MemoryStream();
        below.append(new byte[100], 0, 100);
        final StrictStream strict = new StrictStream(below);
        final CountDownLatch entered = new CountDownLatch(1);
        final CountDownLatch release = new CountDownLatch(1);
        strict.setHook((op, n) -> {
            if (op == StrictStream.Op.APPEND && entered.getCount() > 0) {
                entered.countDown();
                try {
                    if (!release.await(5, TimeUnit.SECONDS)) {
                        throw new IOException("the test did not release the append");
                    }
                } catch (InterruptedException e) {
                    Thread.currentThread().interrupt();
                    throw new IOException(e);
                }
            }
        });
        final AppendOnlyStream s;
        synchronized (writeLock) {
            s = create(impl, strict, 1000, 10);
        }
        final AtomicReference<Throwable> thrown = new AtomicReference<Throwable>();
        Thread writer = null;
        try {
            synchronized (writeLock) {
                s.append(new byte[300], 0, 300);
            }
            if (!entered.await(5, TimeUnit.SECONDS)) {
                throw new AssertionError("the buffer's thread did not append");
            }
            writer = new Thread(() -> {
                synchronized (writeLock) {
                    try {
                        call.run(s);
                    } catch (Throwable e) {
                        thrown.set(e);
                    }
                }
            }, "StorageContractTester-writer");
            writer.start();
            writer.join(200);
        } finally {
            release.countDown();
            if (writer != null) {
                writer.join();
            }
            synchronized (writeLock) {
                try {
                    s.close();
                } catch (IOException e) {
                    // A breach made the flush fail; it is reported below.
                }
            }
        }
        Throwable failure = null;
        for (StrictStream.Breach b : strict.breaches()) {
            if (b.kind == StrictStream.Kind.OVERLAP) {
                failure = b;
            } else {
                results.record(impl + " on StrictStream", name + ": " + b.kind, b, true);
            }
        }
        if (failure == null && thrown.get() != null) {
            results.record(impl + " on StrictStream", name, thrown.get(), true);
        }
        results.record(impl, "one writer: " + name, failure, true);
    }

    @Nano
    public static void testOneWriterBufferedStream(TestEnvironment c) throws Exception {
        oneWriter(c, BUFFERED);
    }

    @Nano
    public static void testOneWriterStorageManager(TestEnvironment c) throws Exception {
        oneWriter(c, MANAGER);
    }

    // ======== A workload ========

    /**
     * A workload on a StrictStream, from one seed: a writer that, holding the write lock,
     * appends 1 to 3,000 bytes at a time and now and then cuts, asks for the length and the
     * first position, and syncs; and two readers that read what has been appended and compare
     * it with what was. Each StrictStream breach is a failure; one writer's (bergdb 015-80)
     * is kept, not thrown, while 015-80 is in the skip list, so that the workload goes on.
     */
    static void workload(StreamContract.Results results, final String impl, long seed,
            long millis) throws Exception {
        final Object writeLock = new Object();
        final StrictStream strict = new StrictStream(new MemoryStream());
        boolean known80 = StreamContract.skipped("015-80");
        if (known80) {
            strict.tolerate(StrictStream.Kind.OVERLAP);
        }
        final AppendOnlyStream s;
        synchronized (writeLock) {
            s = create(impl, strict, 10 * 1000, 10);
        }
        final Random random = new Random(seed);
        final long[] published = new long[2];      // the length and the cut, under 'published'
        final AtomicReference<Throwable> readerFailure = new AtomicReference<Throwable>();
        final long end = System.nanoTime() + millis * 1000000L;
        Thread[] readers = new Thread[2];
        for (int r = 0; r < readers.length; r++) {
            final Random rr = new Random(seed * 31 + r);
            readers[r] = new Thread(() -> {
                byte[] dest = new byte[4000];
                while (System.nanoTime() < end && readerFailure.get() == null) {
                    long length, cut;
                    synchronized (published) {
                        length = published[0];
                        cut = published[1];
                    }
                    if (length - cut < 1) {
                        Thread.yield();
                        continue;
                    }
                    long pos = cut + Math.floorMod(rr.nextLong(), length - cut);
                    int n = (int) Math.min(length - pos, 1 + rr.nextInt(dest.length));
                    try {
                        s.read(pos, dest, 0, n);
                        for (int i = 0; i < n; i++) {
                            if (dest[i] != at(pos + i)) {
                                throw new AssertionError("read(" + pos + ", " + n + "): byte "
                                        + dest[i] + " at " + (pos + i) + ", where "
                                        + at(pos + i) + " was appended");
                            }
                        }
                    } catch (ReadBelowFirstPosException e) {
                        synchronized (published) {
                            if (pos >= published[1]) {
                                readerFailure.compareAndSet(null, e);
                            }
                        }
                    } catch (Throwable e) {
                        readerFailure.compareAndSet(null, e);
                    }
                }
            }, "StorageContractTester-reader-" + r);
            readers[r].start();
        }

        Throwable writerFailure = null;
        try {
            long length = 0;
            long cut = 0;
            int op = 0;
            while (System.nanoTime() < end && readerFailure.get() == null) {
                op++;
                synchronized (writeLock) {
                    int n = 1 + random.nextInt(3000);
                    byte[] b = new byte[n];
                    for (int i = 0; i < n; i++) {
                        b[i] = at(length + i);
                    }
                    s.append(b, 0, n);
                    length += n;
                    synchronized (published) {
                        published[0] = length;
                    }
                    if (op % 25 == 0 && length - cut > 20000) {
                        cut = cut + random.nextInt((int) (length - cut - 10000));
                        synchronized (published) {
                            published[1] = cut;
                        }
                        s.pretruncate(cut);
                    }
                    if (op % 10 == 0) {
                        StreamContract.expect("the length", length, s.getLength());
                        long first = s.getFirstPos();
                        if (first > cut) {
                            throw new AssertionError("the first position, " + first
                                    + ", is past the last cut, " + cut);
                        }
                    }
                }
                if (op % 40 == 0) {
                    if (s instanceof StorageManager) {
                        ((StorageManager) s).sync(length);
                    } else {
                        ((BufferedStream) s).flushSoon(length);
                    }
                }
            }
        } catch (Throwable e) {
            writerFailure = e;
        } finally {
            for (Thread r : readers) {
                r.join();
            }
            synchronized (writeLock) {
                try {
                    s.close();
                } catch (IOException e) {
                    if (writerFailure == null) {
                        writerFailure = e;
                    }
                }
            }
        }

        String name = impl + " on StrictStream";
        String what = "the workload, seed " + seed;
        boolean overlap = false;
        for (StrictStream.Breach b : strict.breaches()) {
            if (b.kind == StrictStream.Kind.OVERLAP) {
                if (!overlap) {
                    results.record(impl, "one writer, in " + what, b, false);
                }
                overlap = true;
            } else {
                results.record(name, what + ": " + b.kind, b, false);
            }
        }
        // After a breach of one writer that was thrown, the workload fails with it: that
        // failure is 015-80's too.
        String failed = overlap ? impl : name;
        String failedWhat = overlap ? "one writer, in " + what + ", then" : what + ",";
        if (writerFailure != null) {
            results.record(failed, failedWhat + " the writer", writerFailure, false);
        }
        if (readerFailure.get() != null) {
            results.record(failed, failedWhat + " a reader", readerFailure.get(), false);
        }
        results.record(name, what, null, false);
    }

    private static byte at(long pos) {
        return StreamContract.at(pos);
    }

    @Nano
    public static void testWorkloadBufferedStream(TestEnvironment c) throws Exception {
        StreamContract.Results results = new StreamContract.Results();
        workload(results, BUFFERED, 1, 150);
        results.assertOk(c.out());
    }

    @Nano
    public static void testWorkloadStorageManager(TestEnvironment c) throws Exception {
        StreamContract.Results results = new StreamContract.Results();
        workload(results, MANAGER, 2, 150);
        results.assertOk(c.out());
    }

    /** The workloads for longer, from more seeds: about 20 s. */
    @Nano("night")
    public static void testWorkloadsLong(TestEnvironment c) throws Exception {
        StreamContract.Results results = new StreamContract.Results();
        for (int seed = 100; seed < 120; seed++) {
            workload(results, seed % 2 == 0 ? BUFFERED : MANAGER, seed, 1000);
        }
        results.assertOk(c.out());
    }
}
