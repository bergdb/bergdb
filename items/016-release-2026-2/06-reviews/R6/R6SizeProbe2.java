package bergdb.core;

import bergdb.common.Bytes;
import bergdb.common.StringUtil;
import bergdb.stream.MemoryStream;

/**
 * R6-F1's probe (bergdb 016-06/R6): a record whose size field is enlarged to cover the next
 * record is accepted at a start, and the next record's transaction is gone. Records A, B
 * and C put /a, /b and /c; A's size field is set to A's size plus B's, so that its last
 * byte is B's, LAST_BYTE.
 */
public class R6SizeProbe2 {
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
        byte[] size = new byte[4];
        corrupt.read(a, size, 0, 4);
        int sizeA = Bytes.bytesToIntLE(size, 0);
        int enlarged = (int) (corrupt.getLength() - a) + 4096;   // past the end: recovery's zero fill
        System.out.println("records at " + a + ", " + b + ", " + c + "; A's size " + sizeA
                + " (b - a = " + (b - a) + ") -> " + enlarged);
        Bytes.intToBytesLE(enlarged, size, 0);
        MemoryStream.TestAccess.write(corrupt, size, a);
        try (Db db = Db.builder().testSetup(corrupt).clock(clock)
                .startupDistance(1000000).retainForever().start()) {
            System.out.println("START ACCEPTED: /a=" + str(DbUtil.get(db, Long.MAX_VALUE, "/a"))
                    + ", /b=" + str(DbUtil.get(db, Long.MAX_VALUE, "/b"))
                    + ", /c=" + str(DbUtil.get(db, Long.MAX_VALUE, "/c")));
        } catch (RuntimeException e) {
            System.out.println("START REFUSED: " + e);
        }
    }

    private static String str(byte[] v) {
        return v == null ? "null" : StringUtil.toString(v);
    }
}
