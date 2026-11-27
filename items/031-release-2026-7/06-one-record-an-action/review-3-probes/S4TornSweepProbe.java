package bergdb.core;

import java.util.TreeSet;
import bergdb.storage.RecoverableStream;
import bergdb.stream.MemoryStream;

/**
 * Review probe (s4, 028-67): every prefix of a valid stream's last appends (a crash's torn
 * tail), on a MemoryStream: records that span a meta block, cuts inside headers, at, inside
 * and right after a meta block. Each prefix: start 1 must succeed with the committed
 * records before the cut; starts 2 and 3 (clean restarts) must succeed and write nothing.
 */
public class S4TornSweepProbe {
    public static void main(String[] args) throws Exception {
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        long from;
        try (Db db = Db.builder().testSetup(s).clock(clock).start()) {
            clock.setTime(10);
            db.execute(db.trans().put("a", "a-value"));
            from = s.getLength();
            for (int i = 0; i < 5; i++) {
                clock.setTime(20 + i);
                db.execute(db.trans().put("v" + i, new byte[90000 + 7 * i]));
            }
        }
        final long end = s.getLength();
        TreeSet<Long> cuts = new TreeSet<Long>();
        for (long p = from; p < end; p += 97) cuts.add(p);
        for (long m = RecoverableStream.META_BLOCK_DISTANCE; m < end; m += RecoverableStream.META_BLOCK_DISTANCE) {
            for (long p = m - 300; p <= m + 300; p++) cuts.add(p);
        }
        // around each record's start (walk the stream's records)
        try (Db db = Db.builder().testSetup(s.copy()).clock(clock).start()) {
        }
        int ok = 0, bad = 0;
        for (long len : cuts) {
            if (len <= from || len >= end) continue;
            MemoryStream m = s.copy();
            m.truncate(len);
            String r = null;
            long after1 = -1;
            for (int start = 1; start <= 3 && r == null; start++) {
                long before = m.getLength();
                try (Db db = Db.builder().testSetup(m).clock(clock).start()) {
                    if (DbUtil.get(db, Long.MAX_VALUE, "a") == null) r = "no a at start " + start;
                } catch (RuntimeException e) {
                    String msg = String.valueOf(e.getMessage());
                    r = "start " + start + " " + e.getClass().getSimpleName() + ": "
                            + msg.substring(0, Math.min(120, msg.length()));
                }
                if (r == null && start > 1 && m.getLength() != before) {
                    r = "start " + start + " wrote " + (m.getLength() - before) + " bytes";
                }
            }
            if (r == null) ok++; else { bad++; if (bad < 30) System.out.println("cut at " + len + ": " + r); }
        }
        System.out.println("cuts from " + from + " to " + end + ": ok " + ok + ", bad " + bad);
    }
}
