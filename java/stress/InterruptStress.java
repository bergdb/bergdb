package bergdb.core;

import java.io.File;
import java.io.InterruptedIOException;
import java.util.Map;
import java.util.Random;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.AtomicReference;

import bergdb.pub.util.Clock;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.pub.util.SyncLevel;
import bergdb.storage.StreamIoException;
import bergdb.stream.FileStream;

/**
 * Interrupts everywhere (2026-10-27, bergdb 005-46). A database on a FileStream with reclaim
 * (a retention of 2 s on a test clock, a startup distance of 20 KB, so that it cuts often),
 * eviction (a small budget, so that gets read the stream), a writer with a sync every tenth
 * commit, readers of random keys, and a restart now and then; meanwhile a thread interrupts
 * the workers at random, about every 100 microseconds, and BergDB's storage threads every
 * 100 ms. The rule: no interrupt fails the database or hangs it; only a sync throws for an
 * interrupt (a StreamIoException whose cause is an InterruptedIOException); a read may expire
 * as a cut overtakes it (LookupTimeNotAvailableException, 011-04, W1); every value read names
 * its key; and a call that began with the interrupt flag set, or got it during the call, ends
 * with the flag set.
 *
 * Usage: java -ea -cp bergdb.jar:stress bergdb.core.InterruptStress [seconds [dir]]
 * Prints INTERRUPT STRESS OK, or an error and exits 1.
 */
public class InterruptStress {
    static final long SEC = Clock.UNITS_PER_SEC;
    static final int KEYS = 50000;

    final int seconds;
    final File dir;
    final CoreTestClock clock = new CoreTestClock();
    volatile Db db;
    volatile boolean stop = false;
    final AtomicReference<Throwable> failure = new AtomicReference<Throwable>();
    final Object dbLock = new Object();     // the restart, against the readers' use of db

    InterruptStress(int seconds, File dir) {
        this.seconds = seconds;
        this.dir = dir;
    }

    /** A worker: counts the interrupts it was sent, so that it can check the flag after a call. */
    abstract class Worker extends Thread {
        final AtomicLong sent = new AtomicLong();
        long calls, flagsKept, interruptsSeen;

        Worker(String name) {
            super(name);
            setDaemon(true);
        }

        /** Interrupts this worker and counts it, at once as seen from call(). */
        synchronized void send() {
            interrupt();
            sent.incrementAndGet();
        }

        /**
         * Runs a call and checks the rule for the flag: if an interrupt was sent before the
         * call ended, and after the last check, the flag is set when the call is over.
         */
        void call(Runnable r) {
            long before;
            boolean had;
            synchronized (this) {
                before = sent.get();
                had = Thread.currentThread().isInterrupted();
            }
            try {
                r.run();
            } finally {
                long after;
                boolean flag;
                synchronized (this) {
                    after = sent.get();
                    flag = Thread.interrupted();
                }
                calls++;
                if (had || after > before) {
                    interruptsSeen++;
                    if (!flag) {
                        throw new AssertionError(getName() + ": a call lost the interrupt flag");
                    }
                    flagsKept++;
                }
            }
        }

        public void run() {
            try {
                while (!stop) {
                    once();
                }
            } catch (Throwable e) {
                failure.compareAndSet(null, e);
                stop = true;
            }
        }

        abstract void once() throws Exception;
    }

    static byte[] value(int k, long version) {
        byte[] v = new byte[100];
        v[0] = (byte) (k >> 8);
        v[1] = (byte) k;
        v[2] = (byte) version;
        return v;
    }

    static int keyOf(byte[] v) {
        return ((v[0] & 0xff) << 8) | (v[1] & 0xff);
    }

    Db open() throws Exception {
        DbBuilder b = Db.builder();
        b.testSetupExceptStream();
        Db db = b.stream("main", new FileStream(dir), 1000 * 1000, 10).clock(clock)
                .cacheSizeIndicator(2 * 1000 * 1000).evictionSchedule(Eviction.Schedule.BUDGET, 1)
                .start();
        db.setStartupDistance(20000);
        db.setRetainDuration(2 * SEC);      // Writes nothing after the first start (bergdb 015-87).
        return db;
    }

    void run() throws Exception {
        dir.mkdirs();
        File[] fs = dir.listFiles();
        if (fs != null) for (File f : fs) f.delete();
        clock.setTime(SEC);
        db = open();
        for (int k = 0; k < KEYS; k++) {
            db.execute(db.trans().put("/k" + k, value(k, 0)).build());
        }
        db.sync(SyncLevel.ORDINARY);

        final long[] syncsInterrupted = new long[1];
        final long[] restarts = new long[1];
        final AtomicLong expired = new AtomicLong();
        Worker writer = new Worker("writer") {
            final Random r = new Random(1);
            long version = 1, time = SEC;

            void once() throws Exception {
                final int k = r.nextInt(KEYS);
                final long v = version++;
                synchronized (dbLock) {
                    time += SEC / 100;
                    clock.setTime(time);
                    final Db d = db;
                    call(() -> d.execute(d.trans().put("/k" + k, value(k, v)).build()));
                    if (v % 10 == 0) {
                        call(() -> {
                            try {
                                d.sync(SyncLevel.ORDINARY);
                            } catch (StreamIoException e) {
                                if (!(e.getCause() instanceof InterruptedIOException)) throw e;
                                syncsInterrupted[0]++;
                            }
                        });
                    }
                    if (v % 20000 == 0) {
                        call(() -> d.close());
                        db = open();
                        restarts[0]++;
                    }
                }
            }
        };
        Worker[] readers = new Worker[3];
        for (int i = 0; i < readers.length; i++) {
            final int seed = 100 + i;
            readers[i] = new Worker("reader-" + i) {
                final Random r = new Random(seed);

                void once() {
                    final int k = r.nextInt(KEYS);
                    final Db d = db;
                    call(() -> {
                        byte[] v;
                        try {
                            v = DbUtil.get(d, "/k" + k);
                        } catch (LookupTimeNotAvailableException e) {
                            expired.incrementAndGet();
                            return;
                        } catch (RuntimeException e) {
                            if (d.internal().isActive()) throw e;
                            return;     // The restart closed it.
                        }
                        if (v == null || keyOf(v) != k) {
                            throw new AssertionError("get of /k" + k + " gave "
                                    + (v == null ? "null" : "the value of /k" + keyOf(v)));
                        }
                    });
                }
            };
        }
        final Worker[] all = new Worker[readers.length + 1];
        all[0] = writer;
        System.arraycopy(readers, 0, all, 1, readers.length);
        final long[] storageInterrupts = new long[1];
        Thread interrupter = new Thread(new Runnable() {
            public void run() {
                Random r = new Random(7);
                long nextStorage = System.nanoTime();
                while (!stop) {
                    all[r.nextInt(all.length)].send();
                    if (System.nanoTime() > nextStorage) {
                        for (Map.Entry<Thread, StackTraceElement[]> e
                                : Thread.getAllStackTraces().entrySet()) {
                            String name = e.getKey().getName();
                            if (name.startsWith("BufferedStream-consumer") || name.equals("FileStream-cut")) {
                                e.getKey().interrupt();
                                storageInterrupts[0]++;
                            }
                        }
                        nextStorage = System.nanoTime() + 100 * 1000000L;
                    }
                    long until = System.nanoTime() + 100 * 1000;
                    while (System.nanoTime() < until) Thread.onSpinWait();
                }
            }
        });
        interrupter.setDaemon(true);
        for (Worker w : all) w.start();
        interrupter.start();
        long end = System.nanoTime() + seconds * 1000000000L;
        while (System.nanoTime() < end && failure.get() == null) {
            Thread.sleep(100);
        }
        stop = true;
        for (Worker w : all) {
            w.join(60000);      // a hang guard; 10 s until bergdb 028-23
            if (w.isAlive()) {
                throw new AssertionError(w.getName() + " hung: " + java.util.Arrays.toString(w.getStackTrace()));
            }
        }
        interrupter.join();
        if (failure.get() != null) throw new RuntimeException("a worker failed", failure.get());

        long first = db.getFirstAvailableLookupTime();
        db.execute(db.trans().put("/end", new byte[1]).build());
        db.sync(SyncLevel.ORDINARY);
        db.close();
        long calls = 0, seen = 0;
        for (Worker w : all) {
            calls += w.calls;
            seen += w.interruptsSeen;
        }
        System.out.println("InterruptStress: " + seconds + " s, " + calls + " calls, " + seen
                + " of them with an interrupt, the flag kept by all; syncs ended by an interrupt "
                + syncsInterrupted[0] + "; reads expired by a cut " + expired.get() + "; restarts "
                + restarts[0] + "; storage threads interrupted " + storageInterrupts[0]
                + "; first available lookup time " + first);
        if (first == 0) throw new AssertionError("reclaim made no cut");
    }

    public static void main(String[] args) {
        int seconds = args.length > 0 ? Integer.parseInt(args[0]) : 20;
        File dir = new File(args.length > 1 ? args[1] : "build/interruptstress");
        try {
            new InterruptStress(seconds, dir).run();
        } catch (Throwable e) {
            e.printStackTrace(System.out);
            System.out.println("INTERRUPT STRESS FAILED: " + e);
            System.exit(1);
        }
        System.out.println("INTERRUPT STRESS OK");
        System.exit(0);
    }
}
