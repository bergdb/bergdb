package bergdb.core;

import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.lang.management.ManagementFactory;
import java.lang.management.OperatingSystemMXBean;

import bergdb.pub.CryptoKey;
import bergdb.pub.Database;
import bergdb.pub.DatabaseBuilder;
import bergdb.pub.Factory;
import bergdb.storage.AppendListener;
import bergdb.storage.BufferedStream;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.FileStream;
import bergdb.stream.MemoryStream;

/**
 * Bergdb 005-32: what a start that throws leaves running. Runs today's code.
 *
 * Usage: tools/run.sh CASE [args]; tools/all.sh runs every case as in runs/.
 *   pub DIR N      N starts through the Pub API of a directory whose creation crashed
 *   key DIR N      N starts through the Pub API with a wrong crypto key, then the right one
 *   race DIR N     N times: a start with a main and a replica of two histories fails; a start
 *                  of the main alone follows at once, and writes
 *   closehang      BufferedStream.close() when the last flush fails
 *   twice DIR      two databases started on one directory, writing in turn
 */
public class FailedStartProbe {
    public static void main(String[] args) throws Exception {
        String c = args[0];
        System.out.println("Java " + System.getProperty("java.version"));
        if (c.equals("pub")) pub(new File(args[1]), Integer.parseInt(args[2]));
        else if (c.equals("key")) key(new File(args[1]), Integer.parseInt(args[2]));
        else if (c.equals("race")) race(new File(args[1]), Integer.parseInt(args[2]));
        else if (c.equals("closehang")) closeHang();
        else if (c.equals("twice")) twice(new File(args[1]));
        else throw new IllegalArgumentException(c);
    }

    // ======== pub ========

    static void pub(File root, int n) throws Exception {
        deleteTree(root);
        final File d = new File(root, "db");
        Database database = Factory.database().dir(d.getPath()).start();
        database.sync();
        database.stop();
        Thread.sleep(300);
        truncate(streamFile(d), 200);       // A crash in the creation's first transaction.
        System.out.println("A directory whose creation crashed (its stream cut at 200 bytes); "
                + n + " starts through the Pub API:");
        report("  before", d);
        for (int i = 0; i < n; i++) {
            try {
                Factory.database().dir(d.getPath()).start();
                System.out.println("  started");
            } catch (RuntimeException e) {
                if (i == 0) System.out.println("  each start throws " + e);
            }
        }
        Thread.sleep(500);
        report("  after " + n + " failed starts", d);
        collect();
        report("  after System.gc() and System.runFinalization()", d);
        System.out.println("  the directory removed: " + deleteTree(d));
    }

    // ======== key ========

    static void key(File root, int n) throws Exception {
        deleteTree(root);
        final File d = new File(root, "db");
        CryptoKey right = CryptoKey.generate();
        Database database = Factory.database().dir(d.getPath()).cryptoKey(right).start();
        database.connection().put("/k", "v");
        database.sync();
        database.stop();
        Thread.sleep(300);
        System.out.println("An encrypted database; " + n + " starts with a wrong key, then one "
                + "with the right key:");
        report("  before", d);
        for (int i = 0; i < n; i++) {
            try {
                Factory.database().dir(d.getPath()).cryptoKey(CryptoKey.generate()).start();
                System.out.println("  started with a wrong key");
            } catch (RuntimeException e) {
                if (i == 0) System.out.println("  each start throws " + e);
            }
        }
        Thread.sleep(500);
        report("  after " + n + " failed starts", d);
        Database db2 = Factory.database().dir(d.getPath()).cryptoKey(right).start();
        System.out.println("  the right key: started, /k = " + db2.connection().get("/k", String.class));
        db2.stop();
        Thread.sleep(500);
        report("  after it stopped", d);
        collect();
        report("  after System.gc() and System.runFinalization()", d);
    }

    // ======== race ========

    /**
     * 005-11's P9 in small, with files: the main lost its last two transactions in a crash and
     * started alone once (its recovery zero-filled x); the replica has x and t, whose startup pos
     * is x. A start with both copies t onto the main's buffer and fails (005-28). Then, at once,
     * the main alone starts and writes, while the failed start's buffer is still running.
     */
    static void race(File root, int n) throws Exception {
        java.util.Map<String, Integer> outcomes = new java.util.LinkedHashMap<String, Integer>();
        for (int i = 0; i < n; i++) {
            File d = new File(root, "race-" + i);
            deleteTree(d);
            final File m = new File(d, "main");
            File r = new File(d, "r");
            DbBuilder b = Db.builder();
            b.testSetupExceptStream();
            b.stream("main", new FileStream(m), 100 * 1000, 20);
            b.stream("r", new FileStream(r), 100 * 1000, 20);
            b.startupDistance(10);
            Db db = b.start();
            Trans x = null;
            Trans t = null;
            for (int k = 0; k < 4; k++) {
                x = t;
                t = db.trans().put("/k" + k, "v" + k).build();
                db.execute(t);
            }
            db.close();
            if (t.startupPos != x.tpos || x.nextPos != t.tpos) throw new IllegalStateException();
            truncate(streamFile(m), x.lastPos);         // The crash: x torn, t lost.
            Db alone = startMain(m);                    // Recovery zero-fills x.
            alone.close();

            String o;
            DbBuilder both = Db.builder();
            both.testSetupExceptStream();
            both.stream("main", new FileStream(m), 100 * 1000, 20);
            both.stream("r", new FileStream(r), 100 * 1000, 20);
            try {
                both.start();
                o = "with both: started";
            } catch (RuntimeException e) {
                o = "with both: " + e.getClass().getSimpleName();
            }
            Db main = null;
            try {
                main = startMain(m);
                o += "; the main alone: started";
                final Db fm = main;
                Throwable e = within(5000, new Runnable() {
                    public void run() {
                        fm.execute(fm.trans().put("/new", "v").build());
                        fm.sync(SyncLevel.STRONG);
                    }
                });
                o += e == null ? ", wrote and synced" : ", " + describe(e);
            } catch (RuntimeException e) {
                o += "; the main alone: " + e.getClass().getSimpleName();
            }
            if (main != null) main.stop();
            Thread.sleep(300);
            try {
                final Db again = startMain(m);
                String nv = DbUtil.getString(again, "/new");
                String k2 = DbUtil.getString(again, "/k2");
                o += "; then a start of the main: started, /new = " + nv + ", /k2 = " + k2;
                within(5000, new Runnable() {
                    public void run() {
                        again.close();
                    }
                });
            } catch (RuntimeException e) {
                o += "; then a start of the main: " + e.getClass().getSimpleName();
            }
            Integer count = outcomes.get(o);
            outcomes.put(o, count == null ? 1 : count + 1);
            deleteTree(d);
        }
        System.out.println(n + " times, assertions " + (FailedStartProbe.class.desiredAssertionStatus()
                ? "on" : "off") + ": a start with a main and a replica of two histories fails "
                + "(005-28); at once, the main alone starts and writes:");
        for (java.util.Map.Entry<String, Integer> e : outcomes.entrySet()) {
            System.out.println("  " + e.getKey() + ": " + e.getValue());
        }
    }

    static String describe(Throwable e) {
        if (e.getMessage() != null && e.getMessage().startsWith("HUNG")) {
            return "its write and sync still running after 5 s";
        }
        return "its write or sync: " + e.getClass().getSimpleName() + " (" + cause(e) + ")";
    }

    /** Runs r in a daemon thread; returns what it threw, or null; HUNG after ms. */
    static Throwable within(int ms, final Runnable r) throws InterruptedException {
        final Throwable[] thrown = new Throwable[1];
        Thread th = new Thread() {
            public void run() {
                try {
                    r.run();
                } catch (Throwable e) {
                    thrown[0] = e;
                }
            }
        };
        th.setDaemon(true);
        th.start();
        th.join(ms);
        if (th.isAlive()) return new RuntimeException("HUNG");
        return thrown[0];
    }

    static Db startMain(File m) throws IOException {
        DbBuilder b = Db.builder();
        b.testSetupExceptStream();
        b.stream("main", new FileStream(m), 100 * 1000, 20);
        return b.start();
    }

    static String cause(Throwable e) {
        Throwable c = e;
        while (c.getCause() != null) c = c.getCause();
        String s = c.toString();
        return s.length() > 160 ? s.substring(0, 160) + "..." : s;
    }

    // ======== closehang ========

    static void closeHang() throws Exception {
        final MemoryStream inner = new MemoryStream();
        AppendOnlyStream failing = new AppendOnlyStream() {
            public long getLength() { return inner.getLength(); }
            public long getFirstPos() { return inner.getFirstPos(); }
            public void read(long p, byte[] b, int o, int len) throws IOException {
                inner.read(p, b, o, len);
            }
            public void append(byte[] b, int o, int len) throws IOException {
                throw new IOException("the disk fails");
            }
            public void pretruncate(long p) throws IOException { inner.pretruncate(p); }
            public void seekFirstPos(long p) { throw new UnsupportedOperationException(); }
            public void close() { inner.close(); }
        };
        final BufferedStream b = new BufferedStream(failing, 1000, 20);
        b.setAppendListener(new AppendListener() {
            public void dataAppended(long length) {}
            public void appendFailed(IOException e) {}
        });
        b.start();
        b.append(new byte[100], 0, 100);
        Thread t = new Thread() {
            public void run() {
                try {
                    b.close();
                } catch (IOException e) {
                    // Reported below as not hanging.
                }
            }
        };
        t.setDaemon(true);
        t.start();
        t.join(3000);
        System.out.println("BufferedStream.close() with 100 bytes buffered, and the flush fails: "
                + (t.isAlive() ? "still waiting after 3 s (" + t.getState() + ")" : "returned"));
    }

    // ======== twice ========

    /** Two databases on one directory, in one JVM, writing in turn with a sync each time. */
    static void twice(File root) throws Exception {
        deleteTree(root);
        File d = new File(root, "db");
        Database a = Factory.database().dir(d.getPath()).start();
        a.connection().put("/first", "a");
        a.sync();
        Database b = Factory.database().dir(d.getPath()).start();
        System.out.println("Two databases started on one directory, a and b; each puts and syncs "
                + "in turn, 50 times:");
        int okA = 0;
        int okB = 0;
        String errA = null;
        String errB = null;
        for (int i = 0; i < 50; i++) {
            try {
                a.connection().put("/a" + i, "a" + i);
                a.sync();
                okA++;
            } catch (RuntimeException e) {
                if (errA == null) errA = cause(e);
            }
            try {
                b.connection().put("/b" + i, "b" + i);
                b.sync();
                okB++;
            } catch (RuntimeException e) {
                if (errB == null) errB = cause(e);
            }
        }
        System.out.println("  a: " + okA + " synced puts" + (errA == null ? "" : "; first error: " + errA));
        System.out.println("  b: " + okB + " synced puts" + (errB == null ? "" : "; first error: " + errB));
        a.stop();
        b.stop();
        Thread.sleep(500);
        Database c = Factory.database().dir(d.getPath()).start();
        int foundA = 0;
        int foundB = 0;
        for (int i = 0; i < 50; i++) {
            if (c.connection().get("/a" + i, String.class) != null) foundA++;
            if (c.connection().get("/b" + i, String.class) != null) foundB++;
        }
        System.out.println("  a restart: started; it finds " + foundA + " of a's puts and " + foundB
                + " of b's");
        c.stop();
        Thread.sleep(300);
        deleteTree(root);
    }

    // ======== Helpers ========

    static void report(String what, File d) {
        System.out.println(what + ": " + consumers() + " BufferedStream threads; "
                + openFiles() + " open file descriptors in the JVM");
    }

    static int consumers() {
        int n = 0;
        for (Thread t : Thread.getAllStackTraces().keySet()) {
            if (t.getName().startsWith("BufferedStream-consumer") && t.isAlive()) n++;
        }
        return n;
    }

    static long openFiles() {
        OperatingSystemMXBean os = ManagementFactory.getOperatingSystemMXBean();
        if (os instanceof com.sun.management.UnixOperatingSystemMXBean) {
            return ((com.sun.management.UnixOperatingSystemMXBean) os).getOpenFileDescriptorCount();
        }
        return -1;
    }

    @SuppressWarnings("deprecation")
    static void collect() throws InterruptedException {
        for (int i = 0; i < 5; i++) {
            System.gc();
            System.runFinalization();
            Thread.sleep(400);
        }
    }

    static File streamFile(File d) throws IOException {
        File[] fs = d.listFiles();
        File found = null;
        if (fs != null) for (File f : fs) if (f.getName().endsWith(".bergdb")) found = f;
        if (found == null) throw new IOException("no stream file in " + d);
        return found;
    }

    static void truncate(File f, long length) throws IOException {
        RandomAccessFile raf = new RandomAccessFile(f, "rw");
        raf.setLength(length);
        raf.close();
    }

    static boolean deleteTree(File f) {
        File[] fs = f.listFiles();
        if (fs != null) for (File c : fs) deleteTree(c);
        return f.delete() || !f.exists();
    }
}
