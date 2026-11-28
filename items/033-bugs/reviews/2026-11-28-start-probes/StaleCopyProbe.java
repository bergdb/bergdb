package bergdb.core;

import java.io.File;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import bergdb.pub.util.SyncLevel;
import bergdb.stream.FileStream;

/**
 * Review probe (bergdb 033, review of the start, 2026-11-28): 028-67's C3 ties a meta block
 * and a record to a database ID and a stream position. A copy of a database's files has the
 * same ID and the same positions, so its later bytes pass those checks in the database it
 * was copied from, and the other way.
 *
 * A database is made and stopped; its files are copied (the copy is database B, the first
 * stays A). Both then commit puts of the same keys and value sizes, A 60 and B 30, so that
 * their records begin at the same positions. The image is B's file up to the end of its
 * record k, then A's bytes from there to the end of A's record j (a tail of another file's
 * bytes within B's last file, as 035-02 found a kill of a write to leave on APFS, here A's
 * file at the same offsets). B is started on the image. A start that takes only B's own
 * records reads B's values of its first k puts; the tail is refused or left out.
 *
 * Arguments: OUT MODE, MODE "same" (A's and B's records have the same times, as two copies
 * run side by side with one clock), "earlier" (A's records after the copy are earlier than
 * B's, as when A is the state before a restore of a backup, written before B), or "restore"
 * (B has committed nothing since the copy: the image is the copy, then A's bytes from its
 * end, as a kill of B's first write after a restore of the copy over A's files can leave it
 * when the bytes not written begin where the copy ends).
 *
 * Usage, from java/ after build.sh:
 *   javac -d CLASSES -cp build/bergdb.jar PROBES/StartChain.java PROBES/StaleCopyProbe.java
 *   java -ea -cp CLASSES:build/bergdb.jar bergdb.core.StaleCopyProbe OUT same
 */
public class StaleCopyProbe {
    static final long SEC = FileStreamPowerLossTester.SEC;

    public static void main(String[] args) throws Exception {
        File base = new File(args[0]);
        boolean same = args[1].equals("same");
        StartChain.rm(base);
        File a = new File(base, "a"), b = new File(base, "b");
        a.mkdirs();
        CoreTestClock clock = new CoreTestClock();
        long time = SEC;
        clock.setTime(time);
        try (Db db = Db.builder().testSetup(new FileStream(a)).clock(clock).start()) {
            for (int i = 0; i < 20; i++) {
                time += SEC; clock.setTime(time);
                db.execute(db.trans().put("k" + i % 8, value('0', i)).build());
            }
            db.sync(SyncLevel.ORDINARY);
        }
        b.mkdirs();
        for (File f : a.listFiles((d, n) -> n.endsWith(".bergdb"))) {
            Files.copy(f.toPath(), new File(b, f.getName()).toPath());
        }
        long t0 = time;
        List<long[]> ra = run(a, 'A', 60, same ? t0 + 1000 * SEC : t0);
        boolean restore = args[1].equals("restore");
        long copyEnd = new File(b, "00000000000000.bergdb").length();
        List<long[]> rb = restore ? new ArrayList<long[]>() : run(b, 'B', 30, t0 + 1000 * SEC);
        for (int i = 0; i < rb.size(); i++) {
            if (ra.get(i)[0] != rb.get(i)[0]) throw new Error("records not at the same positions");
        }
        Map<String, byte[]> fa = StartChain.files(a), fb = StartChain.files(b);
        if (fa.size() != 1 || fb.size() != 1) throw new Error("more than one file");
        String name = fa.keySet().iterator().next();
        int k = 12, j = 45;
        int from = restore ? (int) copyEnd : (int) rb.get(k)[1], to = (int) ra.get(j)[1];     // record ends
        byte[] image = Arrays.copyOf(fb.get(name), to);
        System.arraycopy(fa.get(name), from, image, from, to - from);
        Files.write(new File(b, name).toPath(), image);
        System.out.println("mode " + args[1] + ": B's file, B's bytes to " + from + (restore
                ? " (the end of the copy)" : " (the end of its record " + k + " after the copy)")
                + ", then A's bytes to " + to + " (the end of A's record " + j + ")");
        clock.setTime(t0 + 5000 * SEC);
        try (Db db = Db.builder().testSetup(new FileStream(b)).clock(clock).start()) {
            int own = 0, others = 0, older = 0;
            for (int i = 0; i < 8; i++) {
                byte[] v = DbUtil.get(db, Long.MAX_VALUE, "k" + i);
                if (v[0] == 'A') others++; else if (v[0] == 'B') own++; else older++;
            }
            System.out.println("B started: of its 8 keys, " + others + " read a value that A"
                    + " wrote after the copy, " + own + " one that B wrote, " + older + " one from before the copy; "
                    + "stream length " + db.getStreamLength());
            System.out.println(others > 0 ? "TAKEN: B holds A's records" : "not taken");
        } catch (RuntimeException e) {
            String m = String.valueOf(e.getMessage());
            System.out.println("B's start refused: " + e.getClass().getSimpleName() + ": "
                    + m.substring(0, Math.min(300, m.length())));
            System.out.println("the file " + (Arrays.equals(image, Files.readAllBytes(new File(b, name).toPath()))
                    ? "as before the start" : "changed by the start"));
        }
        StartChain.rm(base);
    }

    /** Commits 'n' puts with values marked 'mark', the first at 'time' + 1 s; their positions and ends. */
    static List<long[]> run(File dir, char mark, int n, long time) throws Exception {
        List<long[]> records = new ArrayList<long[]>();
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(time);
        try (Db db = Db.builder().testSetup(new FileStream(dir)).clock(clock).start()) {
            for (int i = 0; i < n; i++) {
                time += SEC; clock.setTime(time);
                Trans t = db.trans().put("k" + i % 8, value(mark, i)).build();
                db.execute(t);
                records.add(new long[] {t.tpos, t.nextPos});
            }
            db.sync(SyncLevel.ORDINARY);
        }
        return records;
    }

    static byte[] value(char mark, int i) {
        byte[] v = new byte[1000];
        Arrays.fill(v, (byte) mark);
        v[1] = (byte) i;
        return v;
    }
}
