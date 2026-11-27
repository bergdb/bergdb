package bergdb.core;

import java.io.File;
import java.util.ArrayList;
import java.util.TreeSet;
import bergdb.storage.RecoverableStream;
import bergdb.stream.FileStream;

/**
 * Review probe (s4, 028-67): S4TornSweepProbe on a FileStream (028-60 part 2's zero-tail
 * trimming at the open): prefixes of the last appends; start 1, then two clean restarts.
 */
public class S4TornSweepFileProbe {
    public static void main(String[] args) throws Exception {
        File base = new File(args[0]);
        S4TornFillFileProbe.rm(base);
        File orig = new File(base, "orig");
        orig.mkdirs();
        CoreTestClock clock = new CoreTestClock();
        ArrayList<Long> starts = new ArrayList<Long>();
        long end;
        try (Db db = Db.builder().testSetup(new FileStream(orig)).clock(clock).start()) {
            clock.setTime(10);
            db.execute(db.trans().put("a", "a-value"));
            for (int i = 0; i < 5; i++) {
                clock.setTime(20 + i);
                Trans t = db.trans().put("v" + i, new byte[90000 + 7 * i]).build();
                db.execute(t);
                starts.add(t.tpos);
                end = t.nextPos;
            }
        }
        long last = starts.get(starts.size() - 1);
        TreeSet<Long> cuts = new TreeSet<Long>();
        for (long st : starts) {
            for (long p = st + 1; p <= st + 40; p++) cuts.add(p);
            for (long p = st + 41; p < st + 90000; p += 997) cuts.add(p);
        }
        for (long m = RecoverableStream.META_BLOCK_DISTANCE; m < last + 90000; m += RecoverableStream.META_BLOCK_DISTANCE) {
            for (long p = m - 40; p <= m + 140; p++) cuts.add(p);
        }
        int ok = 0, bad = 0;
        for (long len : cuts) {
            File d = new File(base, "x");
            S4TornFillFileProbe.copy(orig, d);
            S4TornFillFileProbe.cut(d, len);
            String r = null;
            for (int start = 1; start <= 3 && r == null; start++) {
                try (Db db = Db.builder().testSetup(new FileStream(d)).clock(clock).start()) {
                    if (DbUtil.get(db, Long.MAX_VALUE, "a") == null) r = "no a at start " + start;
                } catch (RuntimeException e) {
                    String msg = String.valueOf(e.getMessage());
                    r = "start " + start + " " + e.getClass().getSimpleName() + ": "
                            + msg.substring(0, Math.min(110, msg.length()));
                }
            }
            S4TornFillFileProbe.rm(d);
            if (r == null) ok++; else { bad++; if (bad < 40) System.out.println("cut at " + len + ": " + r); }
        }
        System.out.println("record starts " + starts + "; ok " + ok + ", bad " + bad);
        S4TornFillFileProbe.rm(base);
    }
}
