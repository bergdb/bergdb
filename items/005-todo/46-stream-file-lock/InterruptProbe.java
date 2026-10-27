package bergdb.core;

import java.io.File;
import java.nio.file.Files;
import java.util.Map;

import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.util.Job;
import bergdb.stream.FileStream;

/**
 * Probe for bergdb 005-46: what each operation does today when its thread's interrupt flag is
 * set as it is called, as a cancelled task's thread may have it. For each: whether the call
 * returned or threw, whether the database still works after it, and whether the flag is
 * still set when the call is over. The cut and the wait for room in the write buffer are in
 * InterruptCutProbe. Last, BergDB's own storage thread interrupted, as an application's
 * ThreadGroup.interrupt() would do.
 *
 * Usage: java -ea -cp bergdb.jar:. bergdb.core.InterruptProbe
 */
public class InterruptProbe {
    public static void main(String[] args) throws Exception {
        File root = Files.createTempDirectory("bergdb-46-interrupts-").toFile();
        try {
            run(root);
        } finally {
            remove(root);
        }
    }

    static void run(File root) throws Exception {
        // A FileStream made by an interrupted thread: the builder's dir() and replica() make one.
        File d1 = new File(root, "new");
        call("new FileStream(dir), a directory that does not exist", () -> new FileStream(d1).close());
        File d2 = new File(root, "existing");
        new FileStream(d2).close();
        call("new FileStream(dir), an existing directory", () -> new FileStream(d2).close());

        // A database on disk, made by a thread not interrupted.
        File d3 = new File(root, "db");
        Db db = Db.builder().stream("main", new FileStream(d3)).testId().start();
        for (int i = 0; i < 1000; i++) {
            db.execute(db.trans().put("/k" + i, new byte[100]).build());
        }
        db.sync(SyncLevel.ORDINARY);
        db.close();

        // Started by an interrupted thread.
        final Db[] holder = new Db[1];
        final FileStream s3 = new FileStream(d3);
        call("Db.start(), an existing database", () -> holder[0] = Db.builder().stream("main", s3)
                .testId().start());
        Db db2 = holder[0];
        if (db2 == null) {
            db2 = Db.builder().stream("main", new FileStream(d3)).testId().start();
        }
        final Db d = db2;
        call("a get, the value read from the stream", () -> DbUtil.get(d, "/k7"));
        call("a commit of one put", () -> d.execute(d.trans().put("/x", new byte[100]).build()));
        call("sync()", () -> d.sync(SyncLevel.ORDINARY));
        works(d);

        // close() with transactions still in the write buffer.
        for (int i = 0; i < 100; i++) {
            d.execute(d.trans().put("/y" + i, new byte[100]).build());
        }
        long t0 = System.nanoTime();
        call("Db.close(), the first close, transactions in the write buffer", () -> d.close());
        System.out.println(String.format("  it returned after %.1f ms", (System.nanoTime() - t0) / 1e6));
        Thread.sleep(2000);
        System.out.println("  2 s later, the storage threads still there: " + consumers());
        Db db3 = Db.builder().stream("main", new FileStream(d3)).testId().start();
        byte[] v = DbUtil.get(db3, "/y99");
        System.out.println("  started again: the last transaction is " + (v == null ? "lost" : "there"));
        db3.close();

        // The Pub API: the builder's dir(), which makes a FileStream; a job's join(), here
        // addReplica's.
        call("Factory.database().dir(dir)", () -> Factory.database().dir(new File(root, "pub0")
                .getPath()));
        Database pdb = Factory.database().dir(new File(root, "pub").getPath()).start();
        for (int i = 0; i < 1000; i++) {
            pdb.connection().put("/p" + i, "value " + i);
        }
        final Job job = pdb.addReplica("r", new File(root, "pub-replica").getPath());
        call("Job.join(), of addReplica", () -> job.join());
        pdb.stop();

        // BergDB's own storage thread interrupted.
        File d4 = new File(root, "db4");
        final Db db4 = Db.builder().stream("main", new FileStream(d4)).testId().start();
        db4.execute(db4.trans().put("/a", new byte[100]).build());
        db4.sync(SyncLevel.ORDINARY);
        String before = consumers();
        for (Thread t : Thread.getAllStackTraces().keySet()) {
            if (t.getName().startsWith("BufferedStream-consumer")) t.interrupt();
        }
        Thread.sleep(200);
        System.out.println("the storage thread interrupted: before " + before + "; after "
                + consumers());
        final Throwable[] syncFailure = new Throwable[1];
        Thread syncer = new Thread(() -> {
            try {
                db4.execute(db4.trans().put("/b", new byte[100]).build());
                db4.sync(SyncLevel.ORDINARY);
            } catch (Throwable e) {
                syncFailure[0] = e;
            }
        });
        syncer.setDaemon(true);
        syncer.start();
        syncer.join(3000);
        System.out.println("  then a commit and a sync: " + (syncer.isAlive() ? "the sync still"
                + " waits after 3 s" : syncFailure[0] == null ? "returned" : "threw " + syncFailure[0]));
    }

    interface Call {
        void run() throws Exception;
    }

    static void call(String what, Call c) {
        Thread.currentThread().interrupt();
        String result;
        try {
            c.run();
            result = "returned";
        } catch (Throwable e) {
            result = "threw " + e;
            Throwable root = e;
            while (root.getCause() != null && root.getCause() != root) root = root.getCause();
            if (root != e) result += "; the cause: " + root;
        }
        boolean flag = Thread.interrupted();
        System.out.println(what + ": " + result + "; the flag " + (flag ? "still set" : "cleared"));
    }

    static void works(Db d) {
        try {
            d.execute(d.trans().put("/check", new byte[1]).build());
            DbUtil.get(d, "/check");
            System.out.println("  then the database works");
        } catch (Throwable e) {
            System.out.println("  then the database fails: " + e);
        }
    }

    static String consumers() {
        StringBuilder sb = new StringBuilder();
        for (Map.Entry<Thread, StackTraceElement[]> e : Thread.getAllStackTraces().entrySet()) {
            String name = e.getKey().getName();
            if (name.startsWith("BufferedStream-consumer")) {
                if (sb.length() > 0) sb.append(", ");
                sb.append(name).append(" (").append(e.getKey().getState()).append(")");
            }
        }
        return sb.length() == 0 ? "none" : sb.toString();
    }

    static void remove(File f) {
        File[] fs = f.listFiles();
        if (fs != null) for (File c : fs) remove(c);
        f.delete();
    }
}
