import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Duration;
import bergdb.pub.Factory;
import bergdb.pub.WBuilder;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.NoSuchFileException;
import java.util.*;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicReference;

/**
 * App f5 of 031-08 (part B): a copy of a running database's files, taken while it is written
 * to, and what the documents promise of it. The Pub API's Database ("The files") says to
 * copy a stopped database's files; FileStream's Javadoc ("A backup by a copy of the files",
 * bergdb 028-62), the stream of every Pub database, says more: a copy that lists the files
 * and then copies them in the order of their names, the last one last, begun after a
 * transaction committed since the start and a sync() that returned after it, "holds the
 * stream as a kill of the process would leave it at the moment the copy read the last file's
 * end"; a start on it recovers it as after a kill; a copy that missed a listed file that a
 * cut deleted meanwhile can be refused ("take the copy again"), and a start that takes such
 * a copy deletes the files before the gap.
 *
 * A writer (the Pub API, a startup distance of 5 MB, a retain duration of 1 s on the system
 * clock, so that reclaim cuts and deletes files all the time) commits transactions i = 0, 1,
 * ...: each puts /k/x(i mod 400).bin, a value made from (seed, i) of 100 bytes to 120 kB, and
 * /m/last.txt = i, in one w(); it syncs after one in five. A copier takes copies, each after
 * a sync: S = the last transaction that a sync returned for before the copy began, C = the
 * last that returned before it ended. Ways of copying: "doc" (list, sort by name, copy each,
 * the last one last: FileStream's procedure), "glob" (cp DIR/*.bergdb COPY/, the shell's
 * order is the names'), "cpr" (cp -R DIR/. COPY/, the directory's order; DIR/. copies the
 * directory's contents into COPY with both BSD's and GNU's cp, where GNU's cp -R DIR/ COPY/
 * makes COPY/db, as on Linux in 031-08 on 2026-11-28). Each copy is started
 * by open() and must hold the state after k transactions, S + 1 <= k <= C + 1, every value
 * as written, or be refused only as FileStream allows (a listed file missing from the copy,
 * or a way that is not the documented one, which is printed as a NOTE); a refused start must
 * change no file but by recovery at a torn end.
 *
 * Usage: java -cp bergdb-release.jar:out LiveCopy SEED DIR COPIES [WAYS]
 */
public class LiveCopy {
    static long seed;
    static File base, dbDir;
    static final AtomicInteger committed = new AtomicInteger(-1), synced = new AtomicInteger(-1);
    static int copies, accepted, refusedAllowed, notes, failures;
    static long maxLost;

    public static void main(String[] a) throws Exception {
        seed = Long.parseLong(a[0]);
        base = new File(a[1]);
        int n = Integer.parseInt(a[2]);
        List<String> ways = a.length > 3 ? Arrays.asList(a[3].split(",")) : Arrays.asList("doc", "glob", "cpr");
        Common.rmrf(base);
        base.mkdirs();
        dbDir = new File(base, "db");
        long t0 = System.currentTimeMillis();
        AtomicBoolean stop = new AtomicBoolean();
        AtomicReference<Throwable> wfail = new AtomicReference<>();
        Database db = Factory.database().create(dbDir.getPath()).start();
        db.setStartupDistanceInMb(5);
        db.setRetainDuration(Duration.seconds(1));
        Thread writer = new Thread(() -> {
            try {
                write(db, stop);
            } catch (Throwable e) {
                wfail.set(e);
            }
        });
        writer.start();
        Random r = new Random(seed);
        try {
            while (synced.get() < 5) Thread.sleep(10);
            for (int c = 0; c < n && wfail.get() == null; c++) {
                Thread.sleep(100 + r.nextInt(700));
                String way = ways.get(c % ways.size());
                copyAndCheck(c, way);
            }
        } catch (Common.Fail e) {
            System.out.println("FAILED seed " + seed + ": " + e.getMessage());
            stop.set(true);
            writer.join();
            db.close();
            System.exit(1);
        }
        stop.set(true);
        writer.join();
        db.close();
        if (wfail.get() != null) {
            wfail.get().printStackTrace(System.out);
            System.out.println("FAILED seed " + seed + ": the writer: " + wfail.get());
            System.exit(1);
        }
        if (failures > 0) {
            System.out.println("FAILED seed " + seed + ": " + failures + " of " + copies + " copies");
            System.exit(1);
        }
        Common.rmrf(base);
        System.out.println("OK LiveCopy seed " + seed + ", " + copies + " copies of a running database (" + ways + "), "
                + accepted + " accepted, " + refusedAllowed + " refused as FileStream allows, " + notes + " NOTEs, "
                + (committed.get() + 1) + " transactions written, at most " + maxLost + " committed transactions not in a copy, "
                + (System.currentTimeMillis() - t0) / 1000 + " s");
    }

    static byte[] value(int i) {
        Random r = new Random(seed * 1_000_003L + i);
        int p = r.nextInt(100);
        byte[] v = new byte[p < 70 ? 100 + r.nextInt(2000) : p < 97 ? 2000 + r.nextInt(30_000) : 30_000 + r.nextInt(90_000)];
        r.nextBytes(v);
        return v;
    }

    static void write(Database db, AtomicBoolean stop) {
        Connection c = db.connection();
        for (int i = 0; !stop.get(); i++) {
            WBuilder w = c.w();
            w.put("/k/x" + (i % 400) + ".bin", value(i));
            w.put("/m/last.txt", Integer.toString(i));
            w.execute();
            committed.set(i);
            if (i % 5 == 4) {
                c.sync();
                synced.set(i);
            }
        }
    }

    static void copyAndCheck(int c, String way) throws Exception {
        copies++;
        File copy = new File(base, "copy" + c);
        Common.rmrf(copy);
        copy.mkdirs();
        int s = synced.get();            // a sync returned for it, after a commit since the start
        boolean missed = false;
        String how;
        if (way.equals("doc")) {
            File[] fs = dbDir.listFiles((d, nm) -> nm.endsWith(".bergdb"));
            Arrays.sort(fs, Comparator.comparing(File::getName));
            for (File f : fs) {
                try {
                    Files.copy(f.toPath(), new File(copy, f.getName()).toPath());
                } catch (NoSuchFileException e) {
                    missed = true;        // a cut deleted it after the listing
                }
            }
            how = "listed and copied in name order";
        } else {
            String cmd = way.equals("glob") ? "cp " + dbDir.getPath() + "/*.bergdb " + copy.getPath() + "/"
                    : "cp -R " + dbDir.getPath() + "/. " + copy.getPath() + "/";
            Process p = new ProcessBuilder("sh", "-c", cmd + " 2>&1").start();
            String out = new String(p.getInputStream().readAllBytes());
            p.waitFor();
            if (p.exitValue() != 0 || out.contains("No such file")) missed = true;
            new File(copy, "bergdb.lock").delete();
            how = cmd.replace(base.getPath(), "D");
        }
        int cEnd = committed.get();
        Map<String, String> before = FileHandling.snapshot(copy);
        String outcome;
        try (Database db = Factory.database().open(copy.getPath()).start()) {
            int k = check(db, s, cEnd, "copy " + c + " (" + how + ")");
            accepted++;
            maxLost = Math.max(maxLost, cEnd + 1 - k);
            outcome = "accepted, " + k + " transactions (synced before: " + (s + 1) + ", committed at its end: " + (cEnd + 1) + ")";
        } catch (Common.Fail f) {
            failures++;
            outcome = "WRONG: " + f.getMessage();
        } catch (Throwable t) {
            Map<String, String> after = FileHandling.snapshot(copy);
            String ch = FileHandling.diff(before, after);
            String d = FileHandling.describe(t);
            if (missed) {
                refusedAllowed++;
                outcome = "refused, a listed file was missing (FileStream: take the copy again): " + d;
            } else if (!way.equals("doc")) {
                notes++;
                outcome = "NOTE refused (" + way + ", not FileStream's way of copying): " + d;
            } else {
                failures++;
                outcome = "REFUSED, though no listed file was missing: " + d;
            }
            if (ch != null) outcome += "; the refused start changed: " + ch;
        }
        Common.log("copy " + c + " by " + way + ": " + outcome.substring(0, Math.min(outcome.length(), 1500)));
        if (!outcome.startsWith("WRONG") && !outcome.startsWith("REFUSED")) Common.rmrf(copy);
    }

    /** The state after k transactions, S + 1 <= k <= C + 1, every value as written. */
    static int check(Database db, int s, int cEnd, String what) {
        Connection c = db.connection();
        String last = c.get("/m/last.txt", String.class);
        int k = last == null ? 0 : Integer.parseInt(last) + 1;
        if (k < s + 1) throw new Common.Fail(what + ": holds " + k + " transactions, a sync had returned for " + (s + 1));
        if (k > cEnd + 1) throw new Common.Fail(what + ": holds " + k + " transactions, " + (cEnd + 1) + " had been committed");
        int n = 0;
        for (bergdb.pub.Kv<byte[]> kv : c.usePrimary(byte[].class).dir("/k/").kvs()) {
            int j = Integer.parseInt(kv.key().substring(4, kv.key().length() - 4));
            int i = j + ((k - 1 - j) / 400) * 400;          // the last i < k with i mod 400 = j
            if (i >= k || i < 0 || !Arrays.equals(kv.value(), value(i))) {
                throw new Common.Fail(what + ": " + kv.key() + " is not the value of transaction " + i + " (k = " + k + ")");
            }
            n++;
        }
        if (n != Math.min(k, 400)) throw new Common.Fail(what + ": " + n + " keys, expected " + Math.min(k, 400));
        return k;
    }
}
