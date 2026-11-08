package bergdb.pubimp;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * The DbObject type for an integer, a 64-bit integer like Java's long type: the one integer
 * of format 2, for Java's byte, short, char, int and long, stored in the fewest of 1, 2, 4
 * and 8 bytes (bergdb 020-07, R9; 020-02, section 4.7).
 * The type char for this type is 'l'.
 * 
 * @author Frans Lundberg
 */
public final class DbLong extends DbValue {
    private long value;
    
    public DbLong(long value) {
        super('l');
        this.value = value;
    }
    
    public int getByteSize() {
        return ObjectFormat.integerSize(value);
    }
    
    public int write(byte[] b, int offset) {
        return ObjectFormat.writeInteger(b, offset, value);
    }
    
    public long toLong() {
        return value;
    }
    
    public String toString() {
        return "" + value;
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
        Assert.assertEquals(3 + 9, l0.write(bytes, 3));
        
        DbLong l1 = (DbLong) DbValue.read(bytes, 3);
        
        Assert.assertEquals(111222333444L, l1.toLong());
        
        long[] values = {0, -128, 127, 128, -32768, 32768, Integer.MIN_VALUE, 
                Integer.MAX_VALUE + 1L, Long.MIN_VALUE};
        int[] sizes = {2, 2, 2, 3, 3, 5, 5, 9, 9};
        for (int i = 0; i < values.length; i++) {
            DbLong v = new DbLong(values[i]);
            Assert.assertEquals(sizes[i], v.getByteSize());
            Assert.assertEquals(sizes[i], v.write(bytes, 0));
            Assert.assertEquals(values[i], ((DbLong) DbValue.read(bytes, 0)).toLong());
        }
    }
}