import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Duration;
import bergdb.pub.Factory;

import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.file.Files;
import java.nio.file.StandardCopyOption;
import java.security.MessageDigest;
import java.util.*;

/**
 * App f4 of 031-08 (part B): a user's handling of a stopped database's files, against what
 * Database's Javadoc ("The files", "What a crash keeps") and DatabaseBuilder.start() say. Two
 * databases A and B of the same shape (the Pub API, a startup distance of 5 MB, 500 to 700
 * transactions of puts and deletes of values that name their database and transaction, a
 * sync after each, so that the app knows where each transaction's records end) are made
 * once; A2 is A with reclaim (a retain duration of 1 s and a moving clock), so that it has
 * cut and has a first file after 0. Each case copies a database, changes its files as a
 * user could, takes the SHA-256 of every file, starts it with open(), and checks:
 *   - a refused start: its exception and message (printed for the record), and no file
 *     changed, made or removed (but by recovery at a torn end, which a refusal of a gap may
 *     leave, Db.start(); that is printed);
 *   - an accepted start: the state is exactly the state after the first m transactions,
 *     m those whose records end at or before the cut (each transaction whole or not at
 *     all), never a value of another database; the state again after a stop and a start;
 *   - the documented outcome: the last file deleted, emptied or cut is accepted (a cut
 *     tail); a file missing or cut elsewhere is refused; another database's last file or a
 *     tail of another database's bytes is refused before the start writes, with "The
 *     stream's records end at stream position P" and the way out; a file before a gap is
 *     deleted if it is the database's, else refused with the file named; a database of
 *     release 2026.6 is refused with a message that names 2026.6 (given its directory);
 *     read-only files;
 *   - and then the cause removed (the files put back), the start accepted with every
 *     transaction.
 *
 * Usage: java -cp bergdb-release.jar:out FileHandling SEED DIR [OLD_2026_6_DB]
 */
public class FileHandling {
    static long seed;
    static File base;
    static int cases, refused, accepted, failures;
    static final List<String> notes = new ArrayList<>();

    /** A database made once: its files, and where each transaction's records end. */
    static final class Src {
        String tag;
        File dir;
        List<Long> ends = new ArrayList<>();          // the stream's end after transaction i (synced)
        List<String[]> ops = new ArrayList<>();       // per transaction: key, or key + "\u0000" for a delete
        List<Long> times = new ArrayList<>();         // each transaction's time (the TestClock's, increasing)
        long created;                                 // the stream's end after the creation
    }

    public static void main(String[] a) throws Exception {
        seed = Long.parseLong(a[0]);
        base = new File(a[1]);
        File old = a.length > 2 ? new File(a[2]) : null;
        Common.rmrf(base);
        base.mkdirs();
        long t0 = System.currentTimeMillis();
        try {
            Src A = make("A", new Random(seed), false);
            Src B = make("B", new Random(seed), false);      // the same shape and sizes, another ID and values
            Src R = make("R", new Random(seed + 1), true);   // with reclaim's cuts
            log("A: " + A.ends.size() + " transactions, " + files(A.dir).size() + " files, stream to " + last(A)
                    + "; B the same shape; R with cuts, files from " + firstFileStart(R.dir) + " to " + last(R));
            truncations(A, new Random(seed * 5 + 1));
            missing(A);
            foreign(A, B);
            olderCopy(A);
            readOnly(A);
            gaps(R, B);
            if (old != null && old.isDirectory()) oldRelease(old);
        } catch (Common.Fail e) {
            System.out.println("FAILED seed " + seed + ": " + e.getMessage());
            System.exit(1);
        }
        for (String n : notes) System.out.println("NOTE " + n);
        if (failures > 0) {
            System.out.println("FAILED seed " + seed + ": " + failures + " of " + cases + " cases");
            System.exit(1);
        }
        Common.rmrf(base);
        System.out.println("OK FileHandling seed " + seed + ", " + cases + " cases, " + accepted + " accepted, " + refused
                + " refused, " + foreignValues + " accepted with another database's values (NOTE), " + historyReads + " older states read, " + historyErrors + " older reads that threw, " + (System.currentTimeMillis() - t0) / 1000 + " s");
    }

    // ------------------------------------------------------------------ the databases

    static byte[] value(String tag, int i, int len, Random r) {
        byte[] v = new byte[Math.max(len, 12)];
        r.nextBytes(v);
        byte[] h = (tag + ":" + i + ":").getBytes();
        System.arraycopy(h, 0, v, 0, Math.min(h.length, v.length));
        return v;
    }

    static Src make(String tag, Random shape, boolean reclaim) throws Exception {
        Src s = new Src();
        s.tag = tag;
        s.dir = new File(base, "src-" + tag);
        Random val = new Random(seed * 31 + tag.hashCode());
        bergdb.pub.TestClock tc = new bergdb.pub.TestClock();
        long t = 1_780_000_000_000L * 10_000L;
        tc.setTime(bergdb.pub.Time.units(t));
        Database db = Factory.database().create(s.dir.getPath()).clock(tc).start();
        db.setStartupDistanceInMb(5);
        if (reclaim) db.setRetainDuration(Duration.seconds(1));
        db.sync();
        s.created = streamEnd(s.dir);
        Connection c = db.connection();
        int n = reclaim ? 6000 : 500 + shape.nextInt(200);
        for (int i = 0; i < n; i++) {
            if (reclaim && i > 200 && i % 50 == 0 && firstFileStart(s.dir) >= 1_000_000) break;
            t += 10_000L * (reclaim ? 20 + shape.nextInt(40) : 1 + shape.nextInt(5));
            tc.setTime(bergdb.pub.Time.units(t));
            int ops = shape.nextInt(10) < 8 ? 1 : 2 + shape.nextInt(30);
            bergdb.pub.WBuilder w = c.w();
            List<String> keys = new ArrayList<>();
            Set<String> seen = new HashSet<>();
            for (int j = 0; j < ops; j++) {
                String k = "/k/x" + shape.nextInt(400) + ".bin";
                if (!seen.add(k)) continue;
                if (shape.nextInt(6) == 0) {
                    w.delete(k);
                    keys.add(k + "\u0000");
                } else {
                    int p = shape.nextInt(100);
                    int len = p < 60 ? shape.nextInt(200) : p < 95 ? 200 + shape.nextInt(20_000) : 30_000 + shape.nextInt(300_000);
                    w.put(k, value(tag, i, len, val));
                    keys.add(k + "\u0001" + len);
                }
            }
            bergdb.pub.Transaction tr = w.execute();
            db.sync();
            s.times.add(tr.getTime().units());
            s.ops.add(keys.toArray(new String[0]));
            s.ends.add(streamEnd(s.dir));
        }
        db.close();
        // The values again, to check: regenerate by replay (the same Random order).
        return s;
    }

    /** The state after the first m transactions of src: key -> (tag, i, len). */
    static TreeMap<String, String> stateAfter(Src s, int m) {
        TreeMap<String, String> st = new TreeMap<>();
        for (int i = 0; i < m; i++) {
            for (String k : s.ops.get(i)) {
                if (k.endsWith("\u0000")) st.remove(k.substring(0, k.length() - 1));
                else {
                    int x = k.indexOf('\u0001');
                    st.put(k.substring(0, x), s.tag + ":" + i + ":" + k.substring(x + 1));
                }
            }
        }
        return st;
    }

    static int txBefore(Src s, long pos) {
        int m = 0;
        while (m < s.ends.size() && s.ends.get(m) <= pos) m++;
        return m;
    }

    static long last(Src s) { return s.ends.get(s.ends.size() - 1); }

    // ------------------------------------------------------------------ the cases

    static void truncations(Src A, Random r) throws Exception {
        List<File> fs = files(A.dir);
        File lastF = fs.get(fs.size() - 1);
        long s0 = SameBytes.fileStart(lastF.getName());
        long len = lastF.length();
        List<Long> cuts = new ArrayList<>();
        cuts.add(0L);
        cuts.add(1L);
        for (Long e : A.ends) if (e > s0 && e < s0 + len) cuts.add(e - s0);          // at a record's end
        Collections.shuffle(cuts, r);
        cuts = new ArrayList<>(cuts.subList(0, Math.min(cuts.size(), 6)));
        for (Long e : A.ends) if (e > s0 && e < s0 + len) { cuts.add(e - s0 - 1); cuts.add(e - s0 + 1); break; }
        for (int k = 0; k < 8; k++) cuts.add(1 + (long) r.nextInt((int) Math.max(1, len - 1)));   // anywhere
        for (long mb = 0; mb < len; mb += 200_000) {          // at and near the meta blocks (each 200,000 bytes)
            long rel = ((s0 + mb + 199_999) / 200_000) * 200_000 - s0;
            for (long d : new long[] {0, 1, 7, 50, 199}) if (rel + d > 0 && rel + d < len) cuts.add(rel + d);
        }
        for (long c : new TreeSet<>(cuts)) {
            final long cut = c;
            runCase("last file " + lastF.getName() + " cut to " + cut + " bytes (stream position " + (s0 + cut) + ")", A,
                    dir -> truncate(new File(dir, lastF.getName()), cut), Expect.ACCEPT, txBefore(A, s0 + cut), null);
        }
        // A file but the last, cut: to a length that is not a multiple of 100,000, and to one that is.
        if (fs.size() >= 3) {
            File mid = fs.get(fs.size() / 2);
            long m0 = SameBytes.fileStart(mid.getName());
            for (long cut : new long[] {mid.length() - 1, mid.length() / 2 + 3, 100_000}) {
                if (cut <= 0 || cut >= mid.length()) continue;
                runCase("file " + mid.getName() + " (not the last) cut to " + cut + " bytes", A,
                        dir -> truncate(new File(dir, mid.getName()), cut), Expect.REFUSE, -1, null);
            }
            // The last two files cut: the one before the last at a multiple of 100,000, the last removed.
            File before = fs.get(fs.size() - 2);
            if (before.length() > 100_000) {
                long b0 = SameBytes.fileStart(before.getName());
                runCase("the last file removed and the one before cut to 100,000", A, dir -> {
                    del(new File(dir, lastF.getName()));
                    truncate(new File(dir, before.getName()), 100_000);
                }, Expect.ACCEPT, txBefore(A, b0 + 100_000), null);
            }
        }
    }

    static void missing(Src A) throws Exception {
        List<File> fs = files(A.dir);
        File lastF = fs.get(fs.size() - 1);
        runCase("the last file " + lastF.getName() + " missing", A, dir -> del(new File(dir, lastF.getName())), Expect.ACCEPT,
                txBefore(A, SameBytes.fileStart(lastF.getName())), null);
        for (int k : new int[] {0, 1, fs.size() / 2, fs.size() - 2}) {
            if (k < 0 || k >= fs.size() - 1) continue;
            File f = fs.get(k);
            runCase("file " + f.getName() + " missing (" + (k + 1) + " of " + fs.size() + ")", A, dir -> del(new File(dir, f.getName())),
                    Expect.REFUSE, -1, null);
        }
        // Every file but the first missing; and created.txt missing (the start writes it again).
        runCase("created.txt missing", A, dir -> del(new File(dir, "created.txt")), Expect.ACCEPT, A.ends.size(), null);
        runCase("all stream files missing, created.txt kept", A, dir -> {
            for (File f : files(dir)) del(f);
        }, Expect.REFUSE, -1, null);
    }

    static void foreign(Src A, Src B) throws Exception {
        List<File> fa = files(A.dir), fb = files(B.dir);
        Map<String, File> bByName = new HashMap<>();
        for (File f : fb) bByName.put(f.getName(), f);
        File lastA = fa.get(fa.size() - 1);
        // B's file of the same name in place of A's: the last, a middle one, the first.
        for (int k : new int[] {fa.size() - 1, fa.size() / 2, 0}) {
            File f = fa.get(k);
            File g = bByName.get(f.getName());
            if (g == null) continue;
            Expect e = Expect.EITHER;
            runCase("B's " + f.getName() + " in place of A's (" + (k + 1) + " of " + fa.size() + ", " + g.length() + " and "
                    + f.length() + " bytes)", A, dir -> copy(g, new File(dir, f.getName())), e, -2, null);
        }
        // Two databases' files mixed: A's first half, B's second half.
        runCase("A's first half of the files and B's second half", A, dir -> {
            for (int k = fa.size() / 2; k < fa.size(); k++) {
                del(new File(dir, fa.get(k).getName()));
            }
            for (int k = fb.size() / 2; k < fb.size(); k++) copy(fb.get(k), new File(dir, fb.get(k).getName()));
        }, Expect.EITHER, -2, null);
        // B's last file appended after A's (a file that begins where A's last ends): B's bytes in A's tail.
        long endA = SameBytes.fileStart(lastA.getName()) + lastA.length();
        for (File g : fb) {
            long gs = SameBytes.fileStart(g.getName());
            if (gs > SameBytes.fileStart(lastA.getName())) {
                // B's bytes written over the end of A's last file, as a tail of another database.
                runCase("bytes of B's " + g.getName() + " appended to A's last file", A, dir -> {
                    byte[] b = Files.readAllBytes(g.toPath());
                    try (RandomAccessFile raf = new RandomAccessFile(new File(dir, lastA.getName()), "rw")) {
                        raf.seek(raf.length());
                        raf.write(b, 0, Math.min(b.length, 150_000));
                    }
                }, Expect.REFUSE_TAIL, -1, null);
                break;
            }
        }
        // A tail of garbage, and of zeros, after the last record.
        runCase("1,000 random bytes appended to the last file", A, dir -> {
            byte[] b = new byte[1000];
            new Random(seed).nextBytes(b);
            append(new File(dir, lastA.getName()), b);
        }, Expect.REFUSE_TAIL, -1, null);
        runCase("100 zero bytes appended to the last file", A, dir -> append(new File(dir, lastA.getName()), new byte[100]),
                Expect.ACCEPT, A.ends.size(), null);
        runCase("9 MB of zero bytes appended to the last file", A, dir -> append(new File(dir, lastA.getName()),
                new byte[9_000_000]), Expect.REFUSE_TAIL, -1, null);
        // B's whole directory's stream files in A's directory with A's created.txt.
        runCase("B's stream files with A's created.txt", A, dir -> {
            for (File f : files(dir)) del(f);
            for (File g : fb) copy(g, new File(dir, g.getName()));
        }, Expect.EITHER, -3, null);
    }

    static void olderCopy(Src A) throws Exception {
        // An older copy of A: A's files as they were after half its transactions are not kept,
        // so a copy is taken from a shorter database of the same seed (the same bytes up to it).
        Src half = new Src();
        half.tag = "A";
        File older = new File(base, "src-A-older");
        // The files of A up to the end of transaction h, by cutting A's copy (the same bytes).
        int h = A.ends.size() / 2;
        long end = A.ends.get(h - 1);
        copyDir(A.dir, older);
        for (File f : files(older)) {
            long s0 = SameBytes.fileStart(f.getName());
            if (s0 >= end) del(f);
            else if (s0 + f.length() > end) truncate(f, end - s0);
        }
        // That file, now a middle file of A, put back: shorter than its place.
        File lastOld = files(older).get(files(older).size() - 1);
        List<File> fa = files(A.dir);
        if (!lastOld.getName().equals(fa.get(fa.size() - 1).getName())) {
            runCase("an older copy of " + lastOld.getName() + " (" + lastOld.length() + " bytes) put back", A,
                    dir -> copy(lastOld, new File(dir, lastOld.getName())), Expect.REFUSE, -1, null);
        }
        // The older copy as a whole, with the newer files: put back over the directory.
        runCase("the older copy's files put over the newer ones (later files kept)", A, dir -> {
            for (File f : files(older)) copy(f, new File(dir, f.getName()));
        }, lastOld.getName().equals(fa.get(fa.size() - 1).getName()) ? Expect.ACCEPT : Expect.REFUSE,
                lastOld.getName().equals(fa.get(fa.size() - 1).getName()) ? h : -1, null);
        // The older copy alone: the database as it was (a backup restored).
        runCase("the older copy restored alone", A, dir -> {
            for (File f : files(dir)) del(f);
            for (File f : files(older)) copy(f, new File(dir, f.getName()));
        }, Expect.ACCEPT, h, null);
        Common.rmrf(older);
    }

    static void readOnly(Src A) throws Exception {
        runCase("every stream file read-only", A, dir -> {
            for (File f : files(dir)) f.setWritable(false);
        }, Expect.EITHER, A.ends.size(), dir -> {
            for (File f : files(dir)) f.setWritable(true);
        });
        runCase("the directory read-only", A, dir -> dir.setWritable(false), Expect.EITHER, A.ends.size(),
                dir -> dir.setWritable(true));
    }

    /** Files before a gap: the database's own deleted, another's refused (bergdb 028-66). */
    static void gaps(Src R, Src B) throws Exception {
        long first = firstFileStart(R.dir);
        if (first < 400_000) {
            notes.add("R has no cut before 400,000 (first file at " + first + "): the gap cases skipped");
            return;
        }
        List<File> fb = files(B.dir);
        // B's first file as a leftover before R's first file (a gap after it).
        File g = fb.get(0);
        runCase("B's first file " + g.getName() + " before a gap in R's files", R, dir -> copy(g, new File(dir, g.getName())),
                Expect.REFUSE, -1, null);
        // A leftover of R itself: R's own early file, from a copy of R made before it was cut.
        // Not kept; R's first file copied under an earlier name is another position: refused.
        File r0 = files(R.dir).get(0);
        String earlier = String.format("%014d.bergdb", SameBytes.fileStart(r0.getName()) / 100_000 - 4);
        runCase("R's first file copied under an earlier name, " + earlier + ", before a gap", R,
                dir -> copy(r0, new File(dir, earlier)), Expect.REFUSE, -1, null);
        // A file before a gap that is empty.
        String empty = String.format("%014d.bergdb", 0);
        runCase("an empty file " + empty + " before a gap in R's files", R, dir -> Files.write(new File(dir, empty).toPath(),
                new byte[0]), Expect.EITHER, R.ends.size(), null);
        // A missing file after R's cut: refused (the stream after the gap begins after the cut).
        List<File> fr = files(R.dir);
        if (fr.size() > 3) {
            File m = fr.get(1);
            runCase("R's second file " + m.getName() + " missing", R, dir -> del(new File(dir, m.getName())), Expect.REFUSE, -1,
                    null);
        }
        runCase("R as it is", R, dir -> {}, Expect.ACCEPT, R.ends.size(), null);
    }

    static void oldRelease(File old) throws Exception {
        Src s = new Src();
        s.tag = "old";
        s.dir = old;
        runCase("a database of release 2026.6", s, dir -> {}, Expect.REFUSE, -1, null);
    }

    // ------------------------------------------------------------------ one case

    enum Expect { ACCEPT, REFUSE, REFUSE_TAIL, EITHER }

    interface Mutation { void apply(File dir) throws Exception; }

    /**
     * m: the transactions an accepted start must hold (-1: refused expected; -2: a prefix of
     * A's, any m, but never another database's value; -3: B's state or a refusal).
     */
    static void runCase(String name, Src src, Mutation mutate, Expect expect, int m, Mutation undo) throws Exception {
        cases++;
        File dir = new File(base, "case" + cases);
        Common.rmrf(dir);
        copyDir(src.dir, dir);
        mutate.apply(dir);
        Map<String, String> before = snapshot(dir);
        String outcome;
        boolean ok = true;
        Throwable refusal = null;
        int got = -1;
        try (Database db = Factory.database().open(dir.getPath()).start()) {
            got = checkState(db, src, m, name);
            outcome = "accepted, " + got + " of " + src.ends.size() + " transactions";
            accepted++;
        } catch (Common.Fail f) {
            if (m == -2 && f.getMessage().contains("database")) {
                // Another database's file of the same name and length in place of one, and not the
                // last: the documents allow it (Database, "Errors": the checks are a best effort,
                // and damage that passes them gives wrong values with no error); UB-5.
                outcome = "accepted, and reads give another database's values (best effort, documented): " + f.getMessage();
                notes.add(name + ": " + outcome);
                foreignValues++;
                accepted++;
            } else {
                outcome = "accepted, WRONG STATE: " + f.getMessage();
                ok = false;
            }
        } catch (Throwable t) {
            refusal = t;
            refused++;
            outcome = "refused: " + describe(t);
        }
        Map<String, String> after = snapshot(dir);
        String changes = diff(before, after);
        if (refusal != null && changes != null) {
            ok = false;
            outcome += "; THE REFUSED START CHANGED THE FILES: " + changes;
        }
        if (expect == Expect.ACCEPT && refusal != null) { ok = false; outcome += "; EXPECTED ACCEPTED"; }
        if ((expect == Expect.REFUSE || expect == Expect.REFUSE_TAIL) && refusal == null) {
            ok = false;
            outcome += "; EXPECTED REFUSED";
        }
        if (expect == Expect.REFUSE_TAIL && refusal != null && !String.valueOf(refusal.getMessage()).contains("records end at")) {
            outcome += "; (the message does not say where the stream's records end)";
            notes.add(name + ": refused without \"The stream's records end at stream position P\": " + describe(refusal));
        }
        log("case " + cases + ": " + name + ": " + outcome + (refusal == null && changes != null ? "; the start changed: "
                + changes : ""));
        if (!ok) failures++;
        // Then the cause removed in the same directory (the files put back as they were made,
        // or the permissions back), and the start must take it with every transaction.
        if ((refusal != null || undo != null) && !src.tag.equals("old")) {
            File fix = dir;
            if (undo != null) {
                undo.apply(dir);
            } else {
                Set<String> keep = new HashSet<>();
                for (File f : src.dir.listFiles()) {
                    if (f.getName().equals("bergdb.lock")) continue;
                    keep.add(f.getName());
                    copy(f, new File(dir, f.getName()));
                }
                for (File f : dir.listFiles()) if (!keep.contains(f.getName()) && !f.getName().equals("bergdb.lock")) del(f);
            }
            try (Database db = Factory.database().open(fix.getPath()).start()) {
                int k = checkState(db, src, undo != null && refusal == null ? got : src.ends.size(), name + ", cause removed");
                log("case " + cases + ": the cause removed: accepted, " + k + " transactions");
            } catch (Common.Fail f) {
                failures++;
                log("case " + cases + ": the cause removed: WRONG STATE: " + f.getMessage());
            } catch (Throwable t) {
                failures++;
                ok = false;
                log("case " + cases + ": the cause removed: REFUSED: " + describe(t));
            }
        }
        if (ok) {
            try { undoPerms(dir); Common.rmrf(dir); } catch (IOException e) { /* kept */ }
        }
    }

    static void undoPerms(File dir) {
        dir.setWritable(true);
        File[] fs = dir.listFiles();
        if (fs != null) for (File f : fs) f.setWritable(true);
    }

    /** Checks the state of an accepted start; returns the transactions it holds. */
    static int checkState(Database db, Src src, int m, String what) {
        Connection c = db.connection();
        TreeMap<String, byte[]> got = new TreeMap<>();
        for (bergdb.pub.Kv<byte[]> kv : c.usePrimary(byte[].class).dir("/k/").kvs()) got.put(kv.key(), kv.value());
        // Whose values: every value names its database and transaction.
        int maxI = -1;
        String tag = null;
        for (Map.Entry<String, byte[]> e : got.entrySet()) {
            String h = new String(e.getValue(), 0, Math.min(12, e.getValue().length));
            String t = h.substring(0, Math.max(0, h.indexOf(':')));
            if (tag == null) tag = t;
            if (!t.equals(tag)) throw new Common.Fail(what + ": values of two databases: " + tag + " and " + t + " (" + e.getKey() + ")");
        }
        if (m == -3) {
            // B's stream with A's created.txt: B's state or nothing of A.
            return got.size();
        }
        if (tag != null && !tag.equals(src.tag)) throw new Common.Fail(what + ": a value of database " + tag + " in " + src.tag
                + " (" + got.firstKey() + ")");
        int lo = m >= 0 ? m : 0, hi = m >= 0 ? m : src.ends.size();
        for (int k = hi; k >= lo; k--) {
            TreeMap<String, String> st = stateAfter(src, k);
            if (matches(st, got)) {
                // Also a read of every key by get().
                for (Map.Entry<String, String> e : st.entrySet()) {
                    byte[] v = c.get(e.getKey(), byte[].class);
                    if (v == null || !matches1(e.getValue(), v)) throw new Common.Fail(what + ": get(" + e.getKey() + ") differs");
                }
                checkHistory(c, src, k, what);
                return k;
            }
        }
        throw new Common.Fail(what + ": the state is not the state after " + (m >= 0 ? m + " transactions" : "any prefix")
                + " (" + got.size() + " keys)");
    }

    /** Reads at older times (the retain duration is forever in A and B): 25 states, each the oracle's. */
    static void checkHistory(Connection c, Src src, int k, String what) {
        if (src.times.isEmpty() || src.tag.equals("R")) return;
        Random r = new Random(seed + k);
        for (int q = 0; q < 25 && k > 0; q++) {
            int i = q == 0 ? 0 : r.nextInt(k);
            c.setLookupTime(bergdb.pub.Time.units(src.times.get(i)));
            TreeMap<String, byte[]> got = new TreeMap<>();
            try {
                for (bergdb.pub.Kv<byte[]> kv : c.usePrimary(byte[].class).dir("/k/").kvs()) got.put(kv.key(), kv.value());
            } catch (RuntimeException e) {
                notes.add(what + ": a read at the time of transaction " + i + " threw " + describe(e));
                historyErrors++;
                c.setLookupTime(bergdb.pub.Time.MAX);
                return;
            }
            for (byte[] v : got.values()) {
                String h = new String(v, 0, Math.min(12, v.length));
                if (!h.startsWith(src.tag + ":")) {
                    c.setLookupTime(bergdb.pub.Time.MAX);
                    throw new Common.Fail(what + ": at the time of transaction " + i + ", a value of another database: " + h);
                }
            }
            if (!matches(stateAfter(src, i + 1), got)) {
                c.setLookupTime(bergdb.pub.Time.MAX);
                throw new Common.Fail(what + ": the state at the time of transaction " + i + " is not the oracle's");
            }
            historyReads++;
        }
        c.setLookupTime(bergdb.pub.Time.MAX);
    }

    static int historyReads, historyErrors, foreignValues;

    static boolean matches(TreeMap<String, String> st, TreeMap<String, byte[]> got) {
        if (!st.keySet().equals(got.keySet())) return false;
        for (Map.Entry<String, String> e : st.entrySet()) if (!matches1(e.getValue(), got.get(e.getKey()))) return false;
        return true;
    }

    /** "tag:i:len" against a value. */
    static boolean matches1(String exp, byte[] v) {
        int a = exp.lastIndexOf(':');
        int len = Math.max(12, Integer.parseInt(exp.substring(a + 1)));
        String head = exp.substring(0, a + 1);
        if (v.length != len) return false;
        byte[] h = head.getBytes();
        for (int i = 0; i < Math.min(h.length, v.length); i++) if (v[i] != h[i]) return false;
        return true;
    }

    // ------------------------------------------------------------------ files

    static String describe(Throwable t) {
        StringBuilder sb = new StringBuilder();
        for (Throwable c = t; c != null; c = c.getCause()) {
            if (sb.length() > 0) sb.append(" / cause ");
            String m = String.valueOf(c.getMessage()).replace('\n', ' ');
            sb.append(c.getClass().getSimpleName()).append(": ").append(m.length() > 2000 ? m.substring(0, 2000) + "..." : m);
            if (c.getCause() == c) break;
        }
        return sb.toString();
    }

    static List<File> files(File dir) { return SameBytes.listStreamFiles(dir); }

    static long firstFileStart(File dir) { return SameBytes.fileStart(files(dir).get(0).getName()); }

    static long streamEnd(File dir) {
        List<File> fs = files(dir);
        File l = fs.get(fs.size() - 1);
        return SameBytes.fileStart(l.getName()) + l.length();
    }

    static void truncate(File f, long len) throws IOException {
        try (RandomAccessFile raf = new RandomAccessFile(f, "rw")) { raf.setLength(len); }
    }

    static void append(File f, byte[] b) throws IOException {
        try (RandomAccessFile raf = new RandomAccessFile(f, "rw")) { raf.seek(raf.length()); raf.write(b); }
    }

    static void del(File f) throws IOException { Files.delete(f.toPath()); }

    static void copy(File from, File to) throws IOException {
        Files.copy(from.toPath(), to.toPath(), StandardCopyOption.REPLACE_EXISTING);
    }

    static void copyDir(File from, File to) throws IOException {
        Common.rmrf(to);
        to.mkdirs();
        File[] fs = from.listFiles();
        Arrays.sort(fs, Comparator.comparing(File::getName));
        for (File f : fs) {
            if (f.getName().equals("bergdb.lock") || f.isDirectory()) continue;
            Files.copy(f.toPath(), new File(to, f.getName()).toPath());
        }
    }

    static Map<String, String> snapshot(File dir) throws Exception {
        TreeMap<String, String> m = new TreeMap<>();
        File[] fs = dir.listFiles();
        if (fs == null) return m;
        for (File f : fs) {
            if (f.getName().equals("bergdb.lock")) continue;
            MessageDigest md = MessageDigest.getInstance("SHA-256");
            byte[] b = f.canRead() ? Files.readAllBytes(f.toPath()) : new byte[0];
            m.put(f.getName(), b.length + ":" + Common.hex(md.digest(b)).substring(0, 16));
        }
        return m;
    }

    static String diff(Map<String, String> a, Map<String, String> b) {
        List<String> d = new ArrayList<>();
        for (String k : a.keySet()) if (!b.containsKey(k)) d.add(k + " removed");
        for (String k : b.keySet()) if (!a.containsKey(k)) d.add(k + " made (" + b.get(k).split(":")[0] + " bytes)");
        for (String k : a.keySet()) if (b.containsKey(k) && !a.get(k).equals(b.get(k))) {
            d.add(k + " changed (" + a.get(k).split(":")[0] + " to " + b.get(k).split(":")[0] + " bytes)");
        }
        return d.isEmpty() ? null : String.join(", ", d);
    }

    static void log(String s) { Common.log(s); }
}
