package bergdb.core;

import bergdb.common.Bytes;
import bergdb.common.StringUtil;
import bergdb.stream.MemoryStream;

/**
 * R6's probe of a corrupt startupPos (bergdb 016-06/R6): the last record's startupPos, at
 * offset 16 of its header, is set to the position of the record before it, a later
 * position than any startup pos the take gave. Records A, B and C put /a, /b and /c with
 * a startup distance of 1 MB, so the startup pos never moved (0) and no index node was
 * written after the creation.
 */
public class R6StartupPosProbe3 {
    public static void main(String[] args) throws Exception {
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        long a, b, c;
        try (Db db = Db.builder().testSetup(stream).clock(clock)
                .startupDistance(1000000).retainForever().start()) {
            clock.setTime(10);
            Trans t = db.trans().put("/a", "1").build();
            db.execute(t);
            a = t.tpos;
            clock.setTime(20);
            t = db.trans().put("/b", "2").build();
            db.execute(t);
            b = t.tpos;
            clock.setTime(30);
            t = db.trans().put("/c", "3").build();
            db.execute(t);
            c = t.tpos;
        }
        MemoryStream corrupt = stream.copy();
        byte[] sp = new byte[8];
        corrupt.read(c + 16, sp, 0, 8);
        System.out.println("records at " + a + ", " + b + ", " + c + "; C's startupPos "
                + Bytes.bytesToLongLE(sp, 0) + " -> " + b);
        Bytes.longToBytesLE(Long.getLong("sp", -8), sp, 0);
        MemoryStream.TestAccess.write(corrupt, sp, c + 16);
        try (Db db = Db.builder().testSetup(corrupt).clock(clock)
                .startupDistance(1000000).retainForever().start()) {
            System.out.println("START ACCEPTED: /a=" + str(DbUtil.get(db, Long.MAX_VALUE, "/a"))
                    + ", /b=" + str(DbUtil.get(db, Long.MAX_VALUE, "/b"))
                    + ", /c=" + str(DbUtil.get(db, Long.MAX_VALUE, "/c")));
        } catch (RuntimeException | AssertionError e) {
            System.out.println("START REFUSED: " + e);
        }
    }

    private static String str(byte[] v) {
        return v == null ? "null" : StringUtil.toString(v);
    }
}
