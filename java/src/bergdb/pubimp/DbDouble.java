package bergdb.pubimp;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * The DbObject type for a double value, a 64-bit floating point value: its 64 bits, every
 * NaN stored as the one NaN, 0x7ff8000000000000, and -0.0 kept (bergdb 020-07, R12).
 * The type char for this type is 'd'.
 * 
 * @author Frans Lundberg
 */
public final class DbDouble extends DbValue {
    private double value;
    
    public DbDouble(double value) {
        super('d');
        this.value = value;
    }
    
    public int getByteSize() {
        return ObjectFormat.DOUBLE_SIZE;
    }
    
    public String toString() {
        return "d:" + value;
    }
    
    public int write(byte[] b, int offset) {
        return ObjectFormat.writeDouble(b, offset, Double.doubleToRawLongBits(value));
    }
    
    public double toDouble() {
        return value;
    }
    
    // ---- Tests -------------------------------------------------
    
    @Nano
    public static void test0() {
        Assert.assertEquals(1.2, new DbDouble(1.2).toDouble());
        Assert.assertEquals(Double.MAX_VALUE, new DbDouble(Double.MAX_VALUE).toDouble());
        Assert.assertEquals(Double.NaN, new DbDouble(Double.NaN).toDouble());
    }
    
    @Nano
    public static void testSerialize0() {
        byte[] bytes = new byte[20];
        DbDouble d0 = new DbDouble(12.34);
        Assert.assertEquals(4 + 9, d0.write(bytes, 4));
        DbDouble d1 = (DbDouble) DbValue.read(bytes, 4);
        
        Assert.assertEquals(d0.toDouble(), d1.toDouble());
        
        new DbDouble(Double.longBitsToDouble(0x7ff0000000000001L)).write(bytes, 0);
        Assert.assertEquals(0x7ff8000000000000L, ObjectFormat.doubleBitsAt(bytes, 0));
        new DbDouble(-0.0).write(bytes, 0);
        Assert.assertEquals(0x8000000000000000L, 
                Double.doubleToRawLongBits(((DbDouble) DbValue.read(bytes, 0)).toDouble()));
    }
}