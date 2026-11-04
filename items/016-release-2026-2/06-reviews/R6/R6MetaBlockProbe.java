package bergdb.core;

import bergdb.common.Bytes;
import bergdb.common.StringUtil;
import bergdb.stream.MemoryStream;

/**
 * R6-F3's probe (bergdb 016-06/R6): MetaBlock's format comment says the version is "an int
 * (154 for this version)" at offset 4 and the last byte "1 is used to indicate that the
 * block is valid". The probe prints the first meta block's int at 4 and its last byte, then
 * starts a copy whose meta block's int at 4 is 0x0001009A (65,690): bytes 6 and 7 are not
 * read, and the start is accepted.
 */
public class R6MetaBlockProbe {
    public static void main(String[] args) throws Exception {
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        try (Db db = Db.builder().testSetup(stream).clock(clock).start()) {
            clock.setTime(10);
            db.execute(db.trans().put("/a", "1"));
        }
        byte[] block = new byte[128];
        stream.read(0, block, 0, 128);
        System.out.println("meta block 0: int at 4 = " + Bytes.bytesToIntLE(block, 4)
                + ", last byte = " + block[127]);
        MemoryStream other = stream.copy();
        MemoryStream.TestAccess.write(other, new byte[] {1}, 6);
        other.read(0, block, 0, 128);
        System.out.println("copy: int at 4 = " + Bytes.bytesToIntLE(block, 4));
        try (Db db = Db.builder().testSetup(other).clock(clock).start()) {
            System.out.println("START ACCEPTED: /a=" 
                    + StringUtil.toString(DbUtil.get(db, Long.MAX_VALUE, "/a")));
        } catch (RuntimeException e) {
            System.out.println("START REFUSED: " + e);
        }
    }
}
