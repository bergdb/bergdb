import java.io.File;
import java.lang.ref.WeakReference;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.List;

import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;

/**
 * Probe for bergdb 005-55: what Db.finalize() does today. A database is started through the
 * Pub API, used, and dropped without stop(); then System.gc() runs up to 50 times, 100 ms
 * apart, until the database's storage thread has ended (finalize() calls stop(), whose close
 * ends it). Prints BergDB's threads and the process's open files before, after the start
 * and after the collections, and whether the Database and its Db are still strongly
 * reachable (weak references to them).
 *
 * Usage: java -cp build/bergdb.jar:. FinalizeProbe CASE, with CASE one of
 *   mem    an in-memory database, 100 puts;
 *   file   a database in a new temporary directory, 100 puts;
 *   evict  an in-memory database with a 4 MB cache, 400,000 puts in transactions of
 *          10,000, then gets of all of them, so that the eviction thread starts
 *          (bergdb-evictor, item 009).
 * Run it once with finalization on (the default) and once with --finalization=disabled.
 */
public class FinalizeProbe {
    public static void main(String[] args) throws Exception {
        String kind = args[0];
        System.out.println("case " + kind + ", Java " + System.getProperty("java.version"));
        report("before the start");
        WeakReference<?>[] refs = open(kind);
        report("after the start");

        int rounds = 0;
        while (rounds < 50 && count("BufferedStream-consumer") > 0) {
            System.gc();
            Thread.sleep(100);
            rounds++;
        }
        report("after " + rounds + " collections");
        System.out.println("  Database still reachable: " + (refs[0].get() != null)
                + ", its Db still reachable: " + (refs[1].get() != null));
    }

    /** Starts and uses a database; returns weak references to it and to its Db. */
    private static WeakReference<?>[] open(String kind) throws Exception {
        Database database;
        if (kind.equals("file")) {
            File dir = Files.createTempDirectory("finalize-probe").toFile();
            database = Factory.database().dir(dir.getAbsolutePath()).start();
        } else if (kind.equals("evict")) {
            database = Factory.database().memory().cacheSizeInMb(4).start();
        } else {
            database = Factory.database().memory().start();
        }

        WeakReference<?>[] refs = {new WeakReference<Object>(database),
                new WeakReference<Object>(((bergdb.pubimp.DatabaseImp) database).getDb())};
        Connection c = database.connection();
        if (!kind.equals("evict")) {
            for (int i = 0; i < 100; i++) {
                c.put("/k" + i, new byte[10]);
            }
            return refs;
        }

        // Transactions of 10,000 keys, whose index nodes are over the 4 MB budget after the
        // commit's batch (2 ms), so that the commit wakes the eviction thread; then gets of
        // all keys, whose loads wake it too.
        int n = 400 * 1000;
        for (int i = 0; i < n; ) {
            bergdb.pub.WBuilder b = c.w();
            for (int k = 0; k < 10000; k++, i++) {
                b.put("/k" + Integer.toHexString((int) ((long) i * 7919 % n)), new byte[10]);
            }
            b.execute();
        }
        for (int i = 0; i < n; i++) {
            c.get("/k" + Integer.toHexString(i), byte[].class);
        }
        Thread.sleep(200);
        return refs;
    }

    private static void report(String when) {
        List<String> names = new ArrayList<String>();
        for (Thread t : Thread.getAllStackTraces().keySet()) {
            String name = t.getName();
            if (name.startsWith("BufferedStream-") || name.startsWith("bergdb-")
                    || name.startsWith("Db-close-")) {
                names.add(name);
            }
        }
        java.util.Collections.sort(names);
        String[] fds = new File("/dev/fd").list();
        System.out.println("  " + when + ": open files " + (fds == null ? "?" : fds.length)
                + ", threads " + names);
    }

    private static int count(String prefix) {
        int n = 0;
        for (Thread t : Thread.getAllStackTraces().keySet()) {
            if (t.getName().startsWith(prefix)) {
                n++;
            }
        }
        return n;
    }
}
