package bergdb.pubimp;

import bergdb.common.Bytes;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * The DbObject type for a 64-bit integer, like Java's long type.
 * The type char for this type is 'l'.
 * 
 * @author Frans Lundberg
 */
public class DbLong extends DbValue {
    private long value;
    
    public DbLong(long value) {
        super('l');
        this.value = value;
    }
    
    public int getByteSize() {
        return 8;
    }
    
    public int write(byte[] b, int offset) {
        Bytes.longToBytesLE(value, b, offset);
        offset += 8;
        return offset;
    }
    
    public long toLong() {
        return value;
    }
    
    public String toStringValue() {
        return "" + value;
    }
    
    public String toString() {
        return "" + value;
    }
    
    public static DbLong parse(byte[] buffer, int offset) {
        return new DbLong(parseToLong(buffer, offset));
    }
    
    public static long parseToLong(byte[] buffer, int offset) {
        return Bytes.bytesToLongLE(buffer, offset);
    }
    
    
    // ---- Tests -------------------------------------------------
    
    @Nano
    public static void test0() {
        Assert.assertEquals(111222333444L, new DbLong(111222333444L).toLong());
    }
    
    @Nano
    public static void testSerialize0() {
        byte[] bytes = new byte[20];
        DbLong l0 = new DbLong(111222333444L);
        l0.write(bytes, 3);
        
        DbLong l1 = DbLong.parse(bytes, 3);
        
        Assert.assertEquals(111222333444L, l1.toLong());
    }
}