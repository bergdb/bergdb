package bergdb.pubimp;

import bergdb.common.Bytes;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;

/**
 * The DbObject type for a 32-bit integer, like Java's int type.
 * The type char for this type is 'i'.
 * 
 * @author Frans Lundberg
 */
public class DbInt extends DbValue {
    private int value;
    
    public DbInt(int value) {
        super('i');
        this.value = value;
    }
    
    public int getByteSize() {
        return 4;
    }
    
    public int write(byte[] b, int offset) {
        Bytes.intToBytesLE(value, b, offset);
        offset += 4;
        return offset;
    }
    
    public int toInt() {
        return value;
    }
    
    public long toLong() {
        return value;
    }
    
    public float toFloat() {
        return value;
    }
    
    public double toDouble() {
        return value;
    }
    
    public String toStringValue() {
        return "" + value;
    }
    
    public String toString() {
        return "" + value;
    }
    
    public static DbInt parse(byte[] buffer, int offset) {
        return new DbInt(parseToInt(buffer, offset));
    }
    
    public static int parseToInt(byte[] buffer, int offset) {
        int value = Bytes.bytesToIntLE(buffer, offset);
        return value;
    }
    
    // ---- Tests ----------------------------------------------------
    
    @T
    public static void test0() {
        Assert.assertEquals(-1234, new DbInt(-1234).toInt());
    }
    
    @T
    public static void testSerialize0() {
        byte[] bytes = new byte[12];
        DbInt i0 = new DbInt(444555);
        i0.write(bytes, 1);
        DbInt i1 = DbInt.parse(bytes, 1);
        
        Assert.assertEquals(444555, i0.toInt());
        Assert.assertEquals(444555, i1.toInt());
    }
    
    @T
    public static void testToMethods0() {
        DbInt i0 = new DbInt(444555);
        Assert.assertEquals(444555, i0.toInt());
        Assert.assertEquals(444555, i0.toLong());
        Assert.assertEquals(444555.0f, i0.toFloat());
        Assert.assertEquals(444555.0, i0.toDouble());
        Assert.assertEquals((short) 444555, i0.toShort());
        Assert.assertEquals((char) 444555, i0.toChar());
        Assert.assertEquals((byte) 444555, i0.toByte());
    }
    
    @T
    public static void testToMethods1() {
        DbInt i0 = new DbInt(444555);
        Assert.assertEquals("444555", i0.toStringValue());
        Assert.assertEquals(true, i0.toBoolean());
    }
    
}