package bergdb.pubimp;

import bergdb.common.Bytes;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;

/**
 * The DbObject type for a double value, a 64-bit floating point value.
 * The type char for this type is 'd'.
 * 
 * @author Frans Lundberg
 */
public class DbDouble extends DbValue {
    private double value;
    
    public DbDouble(double value) {
        super('d');
        this.value = value;
    }
    
    public int getByteSize() {
        return 8;
    }
    
    public String toString() {
        return "d:" + value;
    }
    
    public int write(byte[] b, int offset) {
        Bytes.doubleToBytesLE(value, b, offset);
        offset += 8;
        return offset;
    }
    
    public long toLong() {
        return (long) value;
    }
    
    public float toFloat() {
        return (float) value;
    }
    
    public double toDouble() {
        return value;
    }
    
    public static DbDouble parse(byte[] buffer, int offset) {
        return new DbDouble(parseToDouble(buffer, offset));
    }
    
    public static double parseToDouble(byte[] buffer, int offset) {
        return Bytes.bytesToDoubleLE(buffer, offset);
    }
    
    // ---- Tests -------------------------------------------------
    
    @T
    public static void test0() {
        Assert.assertEquals(1.2, new DbDouble(1.2).toDouble());
        Assert.assertEquals(Double.MAX_VALUE, new DbDouble(Double.MAX_VALUE).toDouble());
        Assert.assertEquals(Double.NaN, new DbDouble(Double.NaN).toDouble());
    }
    
    @T
    public static void testSerialize0() {
        byte[] bytes = new byte[20];
        DbDouble d0 = new DbDouble(12.34);
        d0.write(bytes, 4);
        DbDouble d1 = DbDouble.parse(bytes, 4);
        
        Assert.assertEquals(d0.toDouble(), d1.toDouble());
    }
}