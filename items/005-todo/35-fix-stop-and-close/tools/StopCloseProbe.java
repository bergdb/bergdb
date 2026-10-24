package bergdb.core;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.FileStream;
import bergdb.stream.MemoryStream;

/**
 * Probes of Db.stop() and Db.close(), bergdb item 005-35 (2026-10-24). Each probe runs the
 * code as it is and prints what it finds; nothing here is a test of the build.
 *
 * Usage: tools/run.sh PROBE DIR (DIR must not exist), or
 *   java -ea -cp bergdb.jar:CLASSES bergdb.core.StopCloseProbe PROBE DIR
 *
 *   stop          puts without a sync, then stop() (core and Pub API) or close(); a restart
 *                 2 s later counts the puts that are in the files
 *   stopclose     stop(), then close(): how long close() takes, and what is still running
 *   twoclose      two threads call close() at once on a database with buffered bytes
 *   running       stop() while a transaction waits for room in the buffer
 *   fullfail      a flush fails while a transaction waits for room in the buffer
 *   exit          a child JVM puts without a sync, stops (Pub API) and returns from main
 *   exit-child    the child of exit
 */
public class StopCloseProbe {
    static final int N = 2000;
    static final String VALUE = "v-0123456789-0123456789-0123456789-0123456789-0123456789";

    public static void main(String[] args) throws Exception {
        String probe = args[0];
        File root = new File(args[1]);
        if (!probe.equals("exit-child")) {
            if (root.exists()) throw new IllegalArgumentException(root + " exists");
            root.mkdirs();
        }
        if (probe.equals("stop")) stop(root);
        else if (probe.equals("stopclose")) stopClose();
        else if (probe.equals("twoclose")) twoClose();
        else if (probe.equals("running")) running();
        else if (probe.equals("fullfail")) fullFail();
        else if (probe.equals("exit")) exit(root);
        else if (probe.equals("exit-child")) exitChild(root);
        else throw new IllegalArgumentException(probe);
        System.exit(0);
    }

    // ======== Helpers ========

    /** An AppendOnlyStream over a MemoryStream whose appends take delayMs: a slow disk. */
    static class SlowStream implements AppendOnlyStream {
        final MemoryStream inner = new MemoryStream();
        final int delayMs;
        volatile boolean closed;
        SlowStream(int delayMs) { this.delayMs = delayMs; }
        public long getLength() { return inner.getLength(); }
        public long getFirstPos() { return inner.getFirstPos(); }
        public void read(long p, byte[] d, int o, int n) throws IOException { inner.read(p, d, o, n); }
        public void append(byte[] s, int o, int n) throws IOException {
            sleep(delayMs);
            inner.append(s, o, n);
        }
        public void pretruncate(long p) throws IOException { inner.pretruncate(p); }
        public void seekFirstPos(long p) throws IOException { inner.seekFirstPos(p); }
        public void close() { closed = true; inner.close(); }
    }

    static void sleep(long ms) {
        try { Thread.sleep(ms); } catch (InterruptedException e) { throw new RuntimeException(e); }
    }

    static int consumerThreads() {
        int n = 0;
        for (Thread t : Thread.getAllStackTraces().keySet()) {
            if (t.getName().startsWith("BufferedStream-consumer") && t.isAlive()) n++;
        }
        return n;
    }

    /** Joins t for up to 3 s; prints where it waits if it is still alive. */
    static void await(Thread t, String what) throws InterruptedException {
        t.join(3000);
        if (t.isAlive()) {
            StringBuilder sb = new StringBuilder("  " + what + " still waits after 3 s, in:");
            StackTraceElement[] st = t.getStackTrace();
            for (int i = 0; i < Math.min(4, st.length); i++) sb.append("\n      at ").append(st[i]);
            System.out.println(sb);
        }
    }

    static double ms(long t0) {
        return (System.nanoTime() - t0) * 1e-6;
    }

    static Db startCore(File dir) throws IOException {
        return Db.builder().mainStream(new FileStream(dir)).start();
    }

    static int countCore(Db db) {
        int n = 0;
        for (int i = 0; i < N; i++) if (DbUtil.get(db, "/k/" + i) != null) n++;
        return n;
    }

    static int countPub(Database d) {
        Connection c = d.connection();
        int n = 0;
        for (int i = 0; i < N; i++) if (c.get("/k/" + i, String.class) != null) n++;
        return n;
    }

    // ======== stop: what a stop leaves in the files ========

    static void stop(File root) throws Exception {
        System.out.println("stop. " + N + " puts of one key each, no sync, then stop() or close();"
                + " 2 s later a restart counts the keys in the files. Defaults: 10 MB buffer, 20 ms.");
        for (int rep = 0; rep < 3; rep++) {
            for (String how : new String[] {"Db.stop()", "Db.close()", "Database.stop()"}) {
                File dir = new File(root, how.replace("()", "").replace('.', '-') + "-" + rep);
                long length;
                if (how.startsWith("Db.")) {
                    Db db = startCore(dir);
                    for (int i = 0; i < N; i++) db.execute(db.trans().put("/k/" + i, VALUE));
                    length = db.getStreamLength();
                    if (how.equals("Db.stop()")) db.stop(); else db.close();
                } else {
                    Database d = Factory.database().dir(dir.getPath()).start();
                    Connection c = d.connection();
                    for (int i = 0; i < N; i++) c.put("/k/" + i, VALUE);
                    length = -1;
                    d.stop();
                }
                sleep(2000);
                long files = 0;
                for (File f : dir.listFiles()) if (f.getName().endsWith(".bergdb")) files += f.length();
                int found;
                if (how.startsWith("Db.")) {
                    Db db2 = startCore(dir);
                    found = countCore(db2);
                    db2.close();
                } else {
                    Database d2 = Factory.database().dir(dir.getPath()).start();
                    found = countPub(d2);
                    d2.stop();
                    sleep(500);
                }
                System.out.println("  " + how + ": stream length at the call "
                        + (length < 0 ? "(not in the Pub API)" : "" + length)
                        + ", in the files 2 s later " + files + "; after a restart " + found
                        + " of " + N + " keys");
            }
        }
    }

    // ======== stopclose: close() after stop() ========

    static void stopClose() throws Exception {
        System.out.println("stopclose. A database on a slow stream (each append 300 ms): puts,"
                + " then stop(), then close().");
        SlowStream s = new SlowStream(300);
        DbBuilder b = Db.builder();
        b.testSetupExceptStream();
        b.stream("main", s, 100 * 1000, 10);
        Db db = b.start();
        sleep(400);     // The creation's bytes are written.
        for (int i = 0; i < 100; i++) db.execute(db.trans().put("/k/" + i, VALUE));
        long length = db.getStreamLength();
        sleep(30);      // The consumer has begun a flush.
        db.stop();
        long t0 = System.nanoTime();
        db.close();
        System.out.printf("  close() returned after %.1f ms; then: consumer threads alive %d,"
                + " stream closed %s, stream length %d of %d%n", ms(t0), consumerThreads(),
                s.closed, s.getLength(), length);
        sleep(1000);
        System.out.printf("  1 s later: consumer threads alive %d, stream closed %s, stream"
                + " length %d of %d%n", consumerThreads(), s.closed, s.getLength(), length);
    }

    // ======== twoclose: two threads close at once ========

    static void twoClose() throws Exception {
        System.out.println("twoclose. A database on a slow stream (each append 300 ms): puts,"
                + " then close() in thread A and, 50 ms later, in thread B.");
        final SlowStream s = new SlowStream(300);
        DbBuilder b = Db.builder();
        b.testSetupExceptStream();
        b.stream("main", s, 100 * 1000, 10);
        final Db db = b.start();
        sleep(400);
        for (int i = 0; i < 100; i++) db.execute(db.trans().put("/k/" + i, VALUE));
        final long length = db.getStreamLength();
        final List<String> out = new ArrayList<String>();
        Thread a = new Thread() {
            public void run() {
                long t0 = System.nanoTime();
                db.close();
                synchronized (out) {
                    out.add(String.format("  A: close() returned after %.1f ms; stream closed %s,"
                            + " length %d of %d", ms(t0), s.closed, s.getLength(), length));
                }
            }
        };
        Thread bt = new Thread() {
            public void run() {
                long t0 = System.nanoTime();
                db.close();
                synchronized (out) {
                    out.add(String.format("  B: close() returned after %.1f ms; stream closed %s,"
                            + " length %d of %d", ms(t0), s.closed, s.getLength(), length));
                }
            }
        };
        a.start();
        sleep(50);
        bt.start();
        a.join();
        bt.join();
        for (String line : out) System.out.println(line);
    }

    // ======== running: stop() while a transaction runs ========

    static void running() throws Exception {
        System.out.println("running. A database on a slow stream (each append 300 ms) with a"
                + " 100 KB buffer: a put of 1 MB runs (it waits for the buffer), and stop() is"
                + " called 100 ms into it.");
        SlowStream s = new SlowStream(300);
        DbBuilder b = Db.builder();
        b.testSetupExceptStream();
        b.stream("main", s, 100 * 1000, 10);
        final Db db = b.start();
        sleep(400);
        final String[] result = new String[1];
        final long[] end = new long[1];
        Thread w = new Thread() {
            public void run() {
                try {
                    db.execute(db.trans().put("/big", new byte[1000 * 1000]));
                    result[0] = "returned normally";
                } catch (Throwable e) {
                    result[0] = "threw " + e;
                }
                end[0] = System.nanoTime();
            }
        };
        w.start();
        sleep(100);
        long t0 = System.nanoTime();
        db.stop();
        long stopped = System.nanoTime();
        System.out.printf("  stop() returned after %.1f ms; the transaction was still running: %s%n",
                (stopped - t0) * 1e-6, w.isAlive());
        await(w, "the transaction");
        if (!w.isAlive()) {
            System.out.printf("  the transaction %s, %.1f ms after stop() returned%n", result[0],
                    (end[0] - stopped) * 1e-6);
        }
    }

    // ======== fullfail: a flush fails while a transaction waits for room ========

    /** A stream whose appends fail once it holds failAt bytes: a disk that fails. */
    static class FailingStream extends SlowStream {
        final long failAt;
        FailingStream(long failAt) { super(10); this.failAt = failAt; }
        public void append(byte[] s, int o, int n) throws IOException {
            if (getLength() + n > failAt) throw new IOException("disk failed (probe)");
            super.append(s, o, n);
        }
    }

    static void fullFail() throws Exception {
        System.out.println("fullfail. A database with a 100 KB buffer on a stream whose appends"
                + " fail after 50 KB: a put of 1 MB, which waits for room in the buffer; then a"
                + " put of 10 bytes in another thread.");
        FailingStream s = new FailingStream(50 * 1000);
        DbBuilder b = Db.builder();
        b.testSetupExceptStream();
        b.stream("main", s, 100 * 1000, 10);
        final Db db = b.start();
        sleep(100);
        Thread w = new Thread() {
            public void run() {
                try {
                    db.execute(db.trans().put("/big", new byte[1000 * 1000]));
                    System.out.println("  the put of 1 MB returned normally");
                } catch (Throwable e) {
                    System.out.println("  the put of 1 MB threw " + e);
                }
            }
        };
        w.start();
        await(w, "the put of 1 MB");
        Thread w2 = new Thread() {
            public void run() {
                try {
                    db.execute(db.trans().put("/small", new byte[10]));
                    System.out.println("  the put of 10 bytes returned normally");
                } catch (Throwable e) {
                    System.out.println("  the put of 10 bytes threw " + e);
                }
            }
        };
        w2.start();
        await(w2, "the put of 10 bytes");
    }

    // ======== exit: the process ends after stop() ========

    static void exit(File root) throws Exception {
        System.out.println("exit. A child JVM puts " + N + " keys without a sync, calls"
                + " Database.stop() and returns from main; then a restart counts the keys.");
        String java = System.getProperty("java.home") + "/bin/java";
        String cp = System.getProperty("java.class.path");
        for (int rep = 0; rep < 3; rep++) {
            File dir = new File(root, "exit-" + rep);
            Process p = new ProcessBuilder(java, "-cp", cp, StopCloseProbe.class.getName(),
                    "exit-child", dir.getPath()).inheritIO().start();
            int code = p.waitFor();
            Database d = Factory.database().dir(dir.getPath()).start();
            int found = countPub(d);
            d.stop();
            sleep(500);
            System.out.println("  child exited with " + code + "; after a restart " + found
                    + " of " + N + " keys");
        }
    }

    static void exitChild(File dir) {
        Database d = Factory.database().dir(dir.getPath()).start();
        Connection c = d.connection();
        for (int i = 0; i < N; i++) c.put("/k/" + i, VALUE);
        d.stop();
        // main returns; System.exit(0) in main()
    }
}
