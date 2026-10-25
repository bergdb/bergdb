package bergdb.core;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.RandomAccessFile;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import bergdb.pub.CryptoKey;
import bergdb.pub.Database;
import bergdb.pub.DatabaseBuilder;
import bergdb.pub.Factory;
import bergdb.pubimp.DatabaseBuilderImp;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.MemoryStream;

/**
 * Bergdb 005-33: what a start does with a database whose creation crashed, and how a
 * creation reaches the stream. Runs today's code.
 *
 * Usage: tools/run.sh CASE [args]; tools/all.sh runs every case as in runs/.
 *   cuts           every cut of a new database's stream: MemoryStream, the core API
 *   pub DIR        cuts through the Pub API, in directories, without and with a crypto key
 *   flushes N      the appends that N creations make to the main stream (the Pub API)
 *   kill DIR N MS  N JVMs killed (SIGKILL) at random moments, 0 to MS ms after they begin to
 *                  create a database
 *   child DIR      used by kill: creates a database in DIR, then waits
 *   replicas       cuts of the main stream and of a replica (the core API), added with
 *                  005-33's change
 */
public class CreationCrashProbe {
    static final int LIMIT_MS = 10 * 1000;

    public static void main(String[] args) throws Exception {
        String c = args[0];
        if (c.equals("cuts")) cuts();
        else if (c.equals("replicas")) replicas();
        else if (c.equals("pub")) pub(new File(args[1]));
        else if (c.equals("flushes")) flushes(Integer.parseInt(args[1]));
        else if (c.equals("kill")) kill(new File(args[1]), Integer.parseInt(args[2]),
                Integer.parseInt(args[3]));
        else if (c.equals("child")) child(new File(args[1]));
        else throw new IllegalArgumentException(c);
    }

    // ======== cuts ========

    /** Every cut of a new database's stream; the outcomes grouped by ranges of cuts. */
    static void cuts() throws Exception {
        MemoryStream s = new MemoryStream();
        Db.builder().testSetup(s).start().close();
        MemoryStream created = s.copy();
        long end = created.getLength();
        System.out.println("A new database's stream (core API, test setup): " + end + " bytes, "
                + "the first meta block (128) and the first transaction (" + (end - 128) + ").");
        System.out.println("A start on the stream cut at each length L from 0 to " + end + ":");
        String group = null;
        long from = 0;
        for (long c = 0; c <= end + 1; c++) {
            String o = c <= end ? cutOutcome(created, c) : "";
            if (!o.equals(group)) {
                if (group != null) {
                    System.out.println("  L = " + (from == c - 1 ? "" + from : from + " to " + (c - 1))
                            + ": " + group);
                }
                group = o;
                from = c;
            }
        }
        // Added with 005-33's change (2026-10-25): the whole creation with its transaction
        // failed, as recovery's zero fill left a cut one before that change.
        MemoryStream failed = created.copy();
        MemoryStream.TestAccess.write(failed, new byte[] {0}, end - 1);
        System.out.println("The whole creation, its transaction failed (its last byte 0): "
                + cutOutcome(failed, end));
    }

    static String cutOutcome(MemoryStream created, long c) throws Exception {
        final MemoryStream m = c == 0 ? new MemoryStream() : created.copy();
        if (c > 0) m.truncate(c);
        final Db db = Db.builder().testSetup(m).build();
        Throwable e = within(new Runnable() {
            public void run() {
                db.start();
            }
        });
        String o;
        if (e == null) {
            db.execute(db.trans().put("/k", "v").build());
            o = "started, " + ("v".equals(DbUtil.getString(db, "/k")) ? "works" : "BROKEN");
        } else {
            o = e.getClass().getSimpleName() + ": " + e.getMessage().replace(": " + c, ": L")
                    .replace("of length " + c + ",", "of length L,");   // since 005-33's change
        }
        db.close();     // Flushes what the start appended, also after a failed start.
        long after = m.getLength();
        return o + "; the stream then " + (after == c ? "unchanged" : after + " bytes");
    }

    // ======== replicas ========

    /** A creation cut in the main stream, in a replica, or in both (the core API). */
    static void replicas() throws Exception {
        MemoryStream s = new MemoryStream();
        Db.builder().testSetup(s).start().close();
        MemoryStream created = s.copy();
        long end = created.getLength();
        System.out.println("A start on a main stream and one replica, each the creation ("
                + end + " bytes) or a cut of it:");
        long[][] cases = {{100, end}, {200, end}, {end, 100}, {end, 200}, {100, 100},
                {200, 200}};
        for (long[] c : cases) {
            final MemoryStream main = created.copy();
            main.truncate(c[0]);
            final MemoryStream replica = created.copy();
            replica.truncate(c[1]);
            DbBuilder b = Db.builder();
            b.testSetupExceptStream();
            b.stream("main", main, 100 * 1000, 10);
            b.stream("r", replica, 100 * 1000, 10);
            final Db db = b.build();
            Throwable e = within(new Runnable() {
                public void run() {
                    db.start();
                }
            });
            String o;
            if (e == null) {
                db.execute(db.trans().put("/k", "v").build());
                o = "started, " + ("v".equals(DbUtil.getString(db, "/k")) ? "works" : "BROKEN");
            } else {
                o = e.getClass().getSimpleName() + ": " + e.getMessage();
            }
            db.close();
            System.out.println("  main " + c[0] + ", replica " + c[1] + ": " + o
                    + "; then main " + main.getLength() + ", replica " + replica.getLength());
        }
    }

    // ======== pub ========

    /** Cuts through the Pub API, in directories (FileStream), without and with a crypto key. */
    static void pub(File root) throws Exception {
        deleteTree(root);
        for (int k = 0; k < 2; k++) {
            CryptoKey key = k == 0 ? null : CryptoKey.generate();
            String what = k == 0 ? "not encrypted" : "encrypted";
            File d = new File(root, "created-" + k);
            Database database = builder(d, key).start();
            database.sync();
            database.stop();
            Thread.sleep(300);      // stop() returns at once; the files close soon after.
            System.out.println("Pub API, " + what + ": a new database's directory: " + list(d));
            File sf = streamFile(d);
            long end = sf.length();
            for (long c : new long[] {0, 1, 64, 127, 128, 129, 132, 133, 200, end - 1, end}) {
                File d2 = new File(root, "cut-" + k + "-" + c);
                copyDir(d, d2);
                truncate(streamFile(d2), c);
                System.out.println("  stream cut at " + c + ": " + pubOutcome(d2, key));
            }
            for (long z : new long[] {128, end}) {
                File d2 = new File(root, "zeros-" + k + "-" + z);
                copyDir(d, d2);
                File f = streamFile(d2);
                truncate(f, 0);
                FileOutputStream out = new FileOutputStream(f);
                out.write(new byte[(int) z]);
                out.close();
                System.out.println("  stream of " + z + " zero bytes: " + pubOutcome(d2, key));
            }
            File d3 = new File(root, "no-stream-" + k);
            copyDir(d, d3);
            if (!streamFile(d3).delete()) throw new IOException("cannot delete");
            System.out.println("  created.txt only, no stream file: " + pubOutcome(d3, key));
        }
    }

    static DatabaseBuilder builder(File d, CryptoKey key) {
        DatabaseBuilder b = Factory.database().dir(d.getPath());
        if (key != null) b.cryptoKey(key);
        return b;
    }

    static String pubOutcome(final File d, final CryptoKey key) throws Exception {
        final Database[] database = new Database[1];
        Throwable e = within(new Runnable() {
            public void run() {
                database[0] = builder(d, key).start();
            }
        });
        String o;
        if (e == null) {
            database[0].connection().put("/k", "v");
            o = "started, " + ("v".equals(database[0].connection().get("/k", String.class))
                    ? "works" : "BROKEN");
            database[0].sync();
            database[0].stop();
        } else {
            o = e.getClass().getSimpleName() + ": " + e.getMessage();
        }
        Thread.sleep(100);
        return o + "; then " + list(d);
    }

    // ======== flushes ========

    /** The appends that n creations make to the main stream, through the Pub API. */
    static void flushes(int n) throws Exception {
        Map<String, Integer> patterns = new LinkedHashMap<String, Integer>();
        long[] firstMs = new long[n];
        for (int i = 0; i < n; i++) {
            final MemoryStream inner = new MemoryStream();
            final List<String> appends = Collections.synchronizedList(new ArrayList<String>());
            final long[] t0 = new long[1];
            AppendOnlyStream rec = new AppendOnlyStream() {
                public long getLength() { return inner.getLength(); }
                public long getFirstPos() { return inner.getFirstPos(); }
                public void read(long p, byte[] b, int o, int len) throws IOException {
                    inner.read(p, b, o, len);
                }
                public void append(byte[] b, int o, int len) throws IOException {
                    if (len > 0) appends.add(len + "@" + (System.nanoTime() - t0[0]) / 100000);
                    inner.append(b, o, len);
                }
                public void pretruncate(long p) throws IOException { inner.pretruncate(p); }
                public void seekFirstPos(long p) throws IOException { inner.seekFirstPos(p); }
                public void close() { inner.close(); }
            };
            DatabaseBuilderImp b = (DatabaseBuilderImp) Factory.database();
            b.mainStream(rec);
            t0[0] = System.nanoTime();
            Database database = b.start();
            long started = (System.nanoTime() - t0[0]) / 100000;
            long deadline = System.currentTimeMillis() + 1000;
            while (inner.getLength() < 264 && System.currentTimeMillis() < deadline) Thread.sleep(1);
            Thread.sleep(50);
            database.stop();
            List<String> sizes = new ArrayList<String>();
            for (String a : appends) sizes.add(a.substring(0, a.indexOf('@')));
            String p = sizes.toString();
            Integer count = patterns.get(p);
            patterns.put(p, count == null ? 1 : count + 1);
            firstMs[i] = appends.isEmpty() ? -1
                    : Long.parseLong(appends.get(0).substring(appends.get(0).indexOf('@') + 1)) - started;
        }
        System.out.println(n + " creations through the Pub API (default buffer: 10 MB, 20 ms); "
                + "the appends to the main stream, by size in bytes, in the first 50 ms after "
                + "the creation is complete:");
        for (Map.Entry<String, Integer> e : patterns.entrySet()) {
            System.out.println("  " + e.getKey() + ": " + e.getValue() + " creations");
        }
        long[] sorted = firstMs.clone();
        java.util.Arrays.sort(sorted);
        System.out.println("Time from start()'s return to the first append (0.1 ms units): min "
                + sorted[0] + ", median " + sorted[n / 2] + ", max " + sorted[n - 1]);
    }

    // ======== kill ========

    static void child(File d) throws Exception {
        System.out.println("CREATING");
        System.out.flush();
        Database database = Factory.database().dir(d.getPath()).start();
        System.out.println("STARTED");
        System.out.flush();
        Thread.sleep(10 * 1000);
        database.stop();
    }

    /** n child JVMs, each killed at a random moment from 0 to ms ms after it begins to create. */
    static void kill(File root, int n, int ms) throws Exception {
        deleteTree(root);
        String java = System.getProperty("java.home") + "/bin/java";
        String cp = System.getProperty("java.class.path");
        Random r = new Random(32);
        Map<String, Integer> outcomes = new LinkedHashMap<String, Integer>();
        Map<String, int[]> delays = new LinkedHashMap<String, int[]>();
        for (int i = 0; i < n; i++) {
            File d = new File(root, "db-" + i);
            Process p = new ProcessBuilder(java, "-cp", cp, CreationCrashProbe.class.getName(),
                    "child", d.getPath()).redirectErrorStream(true).start();
            BufferedReader in = new BufferedReader(new InputStreamReader(p.getInputStream()));
            String line = in.readLine();
            if (!"CREATING".equals(line)) throw new IllegalStateException("child: " + line);
            int delay = r.nextInt(ms + 1);
            Thread.sleep(delay);
            p.destroyForcibly();
            p.waitFor();
            File sf = streamFileOrNull(d);
            long len = sf == null ? -1 : sf.length();
            String state = len == -1 ? "no stream file" : "stream " + len + " bytes";
            String o = state + "; " + pubOutcome(d, null).replaceAll("; then .*", "");
            Integer count = outcomes.get(o);
            outcomes.put(o, count == null ? 1 : count + 1);
            int[] range = delays.get(o);
            if (range == null) delays.put(o, new int[] {delay, delay});
            else delays.put(o, new int[] {Math.min(range[0], delay), Math.max(range[1], delay)});
            deleteTree(d);
        }
        System.out.println(n + " JVMs killed with SIGKILL 0 to " + ms + " ms after they began to "
                + "create a database (Pub API, a directory); what the next start found:");
        for (Map.Entry<String, Integer> e : outcomes.entrySet()) {
            int[] range = delays.get(e.getKey());
            System.out.println("  " + e.getKey() + ": " + e.getValue() + " (killed after "
                    + range[0] + " to " + range[1] + " ms)");
        }
    }

    // ======== Helpers ========

    /** Runs r in a daemon thread; returns what it threw, or null; fails after LIMIT_MS. */
    static Throwable within(final Runnable r) throws InterruptedException {
        final Throwable[] thrown = new Throwable[1];
        Thread t = new Thread() {
            public void run() {
                try {
                    r.run();
                } catch (Throwable e) {
                    thrown[0] = e;
                }
            }
        };
        t.setDaemon(true);
        t.start();
        t.join(LIMIT_MS);
        if (t.isAlive()) return new RuntimeException("HUNG, still running after " + LIMIT_MS + " ms");
        return thrown[0];
    }

    static File streamFile(File d) throws IOException {
        File f = streamFileOrNull(d);
        if (f == null) throw new IOException("no stream file in " + d);
        return f;
    }

    static File streamFileOrNull(File d) {
        File[] fs = d.listFiles();
        if (fs == null) return null;
        File found = null;
        for (File f : fs) {
            if (f.getName().endsWith(".bergdb")) {
                if (found != null) throw new IllegalStateException("two stream files in " + d);
                found = f;
            }
        }
        return found;
    }

    static String list(File d) {
        File[] fs = d.listFiles();
        if (fs == null) return "no directory";
        java.util.Arrays.sort(fs);
        StringBuilder b = new StringBuilder();
        for (File f : fs) {
            if (b.length() > 0) b.append(", ");
            b.append(f.getName()).append(" (").append(f.length()).append(")");
        }
        return b.length() == 0 ? "empty directory" : b.toString();
    }

    static void truncate(File f, long length) throws IOException {
        RandomAccessFile raf = new RandomAccessFile(f, "rw");
        raf.setLength(length);
        raf.close();
    }

    static void copyDir(File from, File to) throws IOException {
        deleteTree(to);
        to.mkdirs();
        for (File f : from.listFiles()) {
            FileInputStream in = new FileInputStream(f);
            FileOutputStream out = new FileOutputStream(new File(to, f.getName()));
            byte[] buf = new byte[8192];
            int n;
            while ((n = in.read(buf)) > 0) out.write(buf, 0, n);
            in.close();
            out.close();
        }
    }

    static void deleteTree(File f) {
        File[] fs = f.listFiles();
        if (fs != null) for (File c : fs) deleteTree(c);
        f.delete();
    }
}
