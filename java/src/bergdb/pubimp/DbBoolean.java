package bergdb.pubimp;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * The DbObject type for storing a boolean; a type that only have two possible values:
 * true or false. The type char for this type is 'n'; stored as Binson's 0x44 or 0x45
 * (bergdb 020-07).
 * 
 * @author Frans Lundberg
 */
public class DbBoolean extends DbValue {
    private boolean value;
    
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

    public boolean toBoolean() {
        return value;
    }
    
    public String toStringValue() {
        return "" + value;
    }
    
    public String toString() {
        return "" + value;
    }
    
    // ---- Tests ----
    
    @Nano
    public static void test0() {
        Assert.assertEquals(true, new DbBoolean(true).toBoolean());
        Assert.assertEquals(false, new DbBoolean(false).toBoolean());
    }
    
    @Nano
    public static void test1() {
        byte[] bytes = new byte[16];
        DbBoolean b0 = new DbBoolean(false);
        
        Assert.assertEquals(4, b0.write(bytes, 3));
        Assert.assertEquals(0x45, bytes[3]);
        DbValue b1 = DbValue.read(bytes, 3);
        
        Assert.assertEquals(false, b0.toBoolean());
        Assert.assertEquals(false, b1.toBoolean());
    }
    
    @Nano
    public static void test2() {
        byte[] bytes = new byte[16];
        DbBoolean b0 = new DbBoolean(true);
        
        Assert.assertEquals(4, b0.write(bytes, 3));
        Assert.assertEquals(0x44, bytes[3]);
        DbValue b1 = DbValue.read(bytes, 3);
        
        Assert.assertEquals(true, b0.toBoolean());
        Assert.assertEquals(true, b1.toBoolean());
    }
}