package bergdb.pubimp;

import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
import bergdb.pub.BadFormatException;

/**
 * The DbObject type for storing a boolean; a type that only have two possible values:
 * true or false. The type char for this type is 'z'.
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
        b[offset] = value == true ? (byte) 1 : (byte) 0;
        offset++;
        return offset;
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
    
    public static DbBoolean parse(byte[] buffer, int offset) {
        return new DbBoolean(parseToBoolean(buffer, offset));
    }
    
    public static boolean parseToBoolean(byte[] buffer, int offset) {
        byte myByte = buffer[offset];
        if (myByte != 0 && myByte != 1) {
            throw new BadFormatException("Expected byte value of 0 or 1, was: " + myByte + ".");
        }
        
        return myByte == 1;
    }
    
    // ---- Tests ----
    
    @T
    public static void test0() {
        Assert.assertEquals(true, new DbBoolean(true).toBoolean());
        Assert.assertEquals(false, new DbBoolean(false).toBoolean());
    }
    
    @T
    public static void test1() {
        byte[] bytes = new byte[16];
        DbBoolean b0 = new DbBoolean(false);
        
        b0.write(bytes, 3);
        DbBoolean b1 = DbBoolean.parse(bytes, 3);
        
        Assert.assertEquals(false, b0.toBoolean());
        Assert.assertEquals(false, b1.toBoolean());
    }
    
    @T
    public static void test2() {
        byte[] bytes = new byte[16];
        DbBoolean b0 = new DbBoolean(true);
        
        b0.write(bytes, 3);
        DbBoolean b1 = DbBoolean.parse(bytes, 3);
        
        Assert.assertEquals(true, b0.toBoolean());
        Assert.assertEquals(true, b1.toBoolean());
    }
}