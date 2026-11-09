package bergdb.pub;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pubimp.ObjectFormat;

/**
 * A double value, a 64-bit floating point number (IEEE 754): its 64 bits, every NaN stored
 * as the one NaN, 0x7ff8000000000000, and -0.0 kept (bergdb 020-07, R12). The type char
 * 'd', DbObject.DOUBLE. Immutable.
 * 
 * @author Frans Lundberg
 */
public final class DbDouble extends DbValue {
    private final double value;
    
    /**
     * A double value; a NaN is stored as the one NaN.
     *
     * @param value  The value.
     */
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
    
    /**
     * The value.
     *
     * @return The value.
     */
    public double toDouble() {
        return value;
    }
    
    // ---- Tests -------------------------------------------------
    
    @Nano
    private static void test0() {
        Assert.assertEquals(1.2, new DbDouble(1.2).toDouble());
        Assert.assertEquals(Double.MAX_VALUE, new DbDouble(Double.MAX_VALUE).toDouble());
        Assert.assertEquals(Double.NaN, new DbDouble(Double.NaN).toDouble());
    }
    
    @Nano
    private static void testSerialize0() {
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