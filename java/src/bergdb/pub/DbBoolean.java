package bergdb.pub;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pubimp.ObjectFormat;

/**
 * A boolean value, true or false: the type char 'n', DbObject.BOOLEAN; stored as Binson's
 * 0x44 or 0x45 (bergdb 020-07). Immutable.
 * 
 * @author Frans Lundberg
 */
public final class DbBoolean extends DbValue {
    private final boolean value;
    
    /**
     * A boolean value.
     *
     * @param value  The value.
     */
    public DbBoolean(boolean value) {
        super('n');
        this.value = value;
    }
    
    public int getByteSize() {
        return 1;
    }
    
    public int write(byte[] b, int offset) {
        return ObjectFormat.writeBoolean(b, offset, value);
    }

    /**
     * The value.
     *
     * @return The value.
     */
    public boolean toBoolean() {
        return value;
    }
    
    public String toString() {
        return "" + value;
    }
    
    // ---- Tests ----
    
    @Nano
    private static void test0() {
        Assert.assertEquals(true, new DbBoolean(true).toBoolean());
        Assert.assertEquals(false, new DbBoolean(false).toBoolean());
    }
    
    @Nano
    private static void test1() {
        byte[] bytes = new byte[16];
        DbBoolean b0 = new DbBoolean(false);
        
        Assert.assertEquals(4, b0.write(bytes, 3));
        Assert.assertEquals(0x45, bytes[3]);
        DbBoolean b1 = (DbBoolean) DbValue.read(bytes, 3);
        
        Assert.assertEquals(false, b0.toBoolean());
        Assert.assertEquals(false, b1.toBoolean());
    }
    
    @Nano
    private static void test2() {
        byte[] bytes = new byte[16];
        DbBoolean b0 = new DbBoolean(true);
        
        Assert.assertEquals(4, b0.write(bytes, 3));
        Assert.assertEquals(0x44, bytes[3]);
        DbBoolean b1 = (DbBoolean) DbValue.read(bytes, 3);
        
        Assert.assertEquals(true, b0.toBoolean());
        Assert.assertEquals(true, b1.toBoolean());
    }
}