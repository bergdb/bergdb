package bergdb.core;

import java.io.File;
import java.io.RandomAccessFile;
import java.nio.file.Files;
import java.util.Arrays;
import bergdb.stream.FileStream;

/**
 * Review probe (s4, 028-67): as S4TornFillProbe, case A, on a FileStream (with 028-60 part
 * 2's trimming of a zero tail at the open): a record torn in its header, start 1 completes
 * it, a kill during that completion's zero fill (the file cut at 'keep' bytes of the record,
 * the rest of the fill lost), start 2.
 */
public class S4TornFillFileProbe {
    static File base;

    public static void main(String[] args) throws Exception {
        base = new File(args[0]);
        int valueSize = Integer.parseInt(args[1]);
        int[] keeps = Arrays.stream(args[2].split(",")).mapToInt(Integer::parseInt).toArray();
        File orig = new File(base, "orig");
        rm(base);
        orig.mkdirs();
        CoreTestClock clock = new CoreTestClock();
        long last;
        try (Db db = Db.builder().testSetup(new FileStream(orig)).clock(clock).start()) {
            clock.setTime(10);
            db.execute(db.trans().put("a", "a-value"));
            clock.setTime(20);
            Trans t = valueSize <= 8000000 ? db.trans().put("b", new byte[valueSize]).build()
                    : db.trans().put("b", new byte[valueSize / 2]).put("c", new byte[valueSize / 2]).build();
            db.execute(t);
            last = t.tpos;
        }
        System.out.println("value " + valueSize + ", last record at " + last);
        int ok = 0, refused = 0;
        for (int cutIn = 1; cutIn < 32; cutIn++) {
            File d1 = new File(base, "c" + cutIn);
            copy(orig, d1);
            cut(d1, last + cutIn);
            try (Db db = Db.builder().testSetup(new FileStream(d1)).clock(clock).start()) {
            }
            for (int keep : keeps) {
                if (keep <= cutIn) continue;
                File d2 = new File(base, "c" + cutIn + "k" + keep);
                copy(d1, d2);
                cut(d2, last + keep);
                String r;
                try (Db db = Db.builder().testSetup(new FileStream(d2)).clock(clock).start()) {
                    r = DbUtil.get(db, Long.MAX_VALUE, "a") != null ? "ok" : "no a";
                } catch (RuntimeException e) {
                    String m = String.valueOf(e.getMessage());
                    r = e.getClass().getSimpleName() + ": " + m.substring(0, Math.min(140, m.length()));
                }
                if (r.equals("ok")) ok++; else refused++;
                if (!r.equals("ok")) System.out.println("cutIn " + cutIn + ", fill cut at " + keep + ": " + r);
                rm(d2);
            }
            rm(d1);
        }
        System.out.println("ok " + ok + ", not ok " + refused);
        rm(base);
    }

    /** Cuts the file stream in 'dir' at stream position 'pos'. */
    static void cut(File dir, long pos) throws Exception {
        File[] fs = dir.listFiles((d, n) -> n.endsWith(".bergdb"));
        Arrays.sort(fs);
        for (File f : fs) {
            long start = Long.parseLong(f.getName().substring(0, 14)) * 100000;
            if (start >= pos) {
                f.delete();
            } else if (start + f.length() > pos) {
                try (RandomAccessFile r = new RandomAccessFile(f, "rw")) {
                    r.setLength(pos - start);
                }
            }
        }
    }

    static void copy(File from, File to) throws Exception {
        to.mkdirs();
        for (File f : from.listFiles()) {
            Files.copy(f.toPath(), new File(to, f.getName()).toPath());
        }
    }

    static void rm(File f) {
        File[] c = f.listFiles();
        if (c != null) for (File x : c) rm(x);
        f.delete();
    }
}
