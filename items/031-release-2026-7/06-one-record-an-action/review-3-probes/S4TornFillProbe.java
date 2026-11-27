package bergdb.core;

import bergdb.stream.MemoryStream;

/**
 * Review probe (s4, 028-67): a crash during the start's own completion of a torn last record,
 * and an APFS zero tail that begins inside a record's header. Each case is a partial append
 * of a valid stream; each start should succeed (the record aborted, "a" kept).
 */
public class S4TornFillProbe {
    public static void main(String[] args) throws Exception {
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        long last;
        int size;
        try (Db db = Db.builder().testSetup(s).clock(clock).start()) {
            clock.setTime(10);
            db.execute(db.trans().put("a", "a-value"));
            clock.setTime(20);
            Trans t = db.trans().put("b", new byte[100 * 1000]).build();
            db.execute(t);
            last = t.tpos;
            size = (int) (t.nextPos - t.tpos);
        }
        System.out.println("last record at " + last + ", size about " + size
                + ", stream length " + s.getLength());

        int ok = 0, refused = 0, other = 0;
        // A. The header cut at 1..31 bytes; start 1 completes it; a crash during that
        // completion leaves the fill cut at 'keep' bytes of the record (start 2).
        for (int cutIn = 1; cutIn < 32; cutIn++) {
            MemoryStream m = s.copy();
            m.truncate(last + cutIn);
            try (Db db = Db.builder().testSetup(m).clock(clock).start()) {
                // start 1: completes the torn record
            }
            for (int keep : new int[] {5, 8, 31, 32, 33, 40, 1000, 10000, 20000}) {
                if (keep <= cutIn || last + keep >= m.getLength()) {
                    continue;
                }
                MemoryStream m2 = m.copy();
                m2.truncate(last + keep);     // a crash during start 1's fill
                String r = start(m2, clock);
                if (r.equals("ok")) ok++; else if (r.startsWith("BadTail")) refused++; else other++;
                if (!r.equals("ok")) {
                    System.out.println("A cutIn " + cutIn + ", fill cut at " + keep + ": " + r);
                }
            }
        }
        // B. A kill leaves zeros from inside the header (byte k) to a length within the
        // record (APFS zero tail, 028-60): the record's own bytes before k.
        for (int k = 4; k < 32; k++) {
            for (int len : new int[] {40, 1000, 5000}) {
                MemoryStream m = s.copy();
                m.truncate(last + len);
                MemoryStream.TestAccess.write(m, new byte[len - k], last + k);
                String r = start(m, clock);
                if (r.equals("ok")) ok++; else if (r.startsWith("BadTail")) refused++; else other++;
                if (!r.equals("ok")) {
                    System.out.println("B zeros from header byte " + k + ", length " + len
                            + ": " + r);
                }
            }
        }
        System.out.println("ok " + ok + ", refused " + refused + ", other " + other);
    }

    private static String start(MemoryStream m, CoreTestClock clock) {
        long before = m.getLength();
        try (Db db = Db.builder().testSetup(m).clock(clock).start()) {
            if (DbUtil.get(db, Long.MAX_VALUE, "a") == null) {
                return "started without a";
            }
            return "ok";
        } catch (RuntimeException e) {
            String msg = String.valueOf(e.getMessage());
            String kind = e.getClass().getSimpleName().equals("BadTailException") ? "BadTail"
                    : "other " + e.getClass().getSimpleName();
            return kind + " written=" + (m.getLength() - before) + ": "
                    + msg.substring(0, Math.min(150, msg.length()));
        }
    }
}
