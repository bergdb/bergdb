package bergdb.pubimp;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * The DbObject type for a byte array.
 * The type char for this type is 'b'.
 * 
 * @author Frans Lundberg
 */
public class DbByteArray extends DbValue {
    private final byte[] value;
    
    /**
     * Creates a new object given a byte array, 'value'.
     * 
     * @param value  
     *      The bytes; copied in this constructor. Not null: BergDB stores no null, a field
     *      without a value is left out (bergdb 020-04).
     */
    public DbByteArray(byte[] value) {
        super('b');
        if (value == null) {
            throw new IllegalArgumentException("value == null not allowed: BergDB stores no "
                    + "null, leave the field out (bergdb 020-04, section 2.4)");
        }
        this.value = value.clone();
    }
    
    private DbByteArray(byte[] value, boolean own) {
        super('b');
        this.value = value;
    }
    
    /** The bytes at 'p' of checked bytes, copied (bergdb 020-07, section 4.1). */
    static DbByteArray read(byte[] b, int p) {
        return new DbByteArray(ObjectFormat.bytesAt(b, p), true);
    }
    
    public int getByteSize() {
        return ObjectFormat.lengthSize(value.length) + value.length;
    }
    
    public String toString() {
        return "b:" + value.length;
    }
    
    public byte[] getByteArray() {
        return value;
    }
    
    public int write(byte[] b, int offset) {
        offset = ObjectFormat.writeBytesHead(b, offset, value.length);
        System.arraycopy(value, 0, b, offset, value.length);
        return offset + value.length;
    }
    
    @SuppressWarnings("unchecked")
    public <TYPE> TYPE toJavaObject(Class<TYPE> c, ClassToObject c2o) {
        // Converts only to byte[].class. Conversions to short[] and so on usually does not
        // make sense. Consider for example the bytes of a JPEG image. Byte array often does
        // not store a number of integers with integer semantics.
        
        Object result;
        
        if (c.equals(byte[].class)) {
            result = value.clone();
        } else {
            result = null;
        }
        return (TYPE) result;
    }
    
    // ---- Tests ----
    
    @Nano
    public static void test0() {
        Assert.assertArrayEquals(new byte[]{1, 2, 3}, 
                new DbByteArray(new byte[]{1, 2, 3}).getByteArray());
    }
    
    @Nano
    public static void testSerialize() {
        byte[] buffer = new byte[100];
        byte[] array = new byte[] {1, 2, -3};
        DbByteArray v0 = new DbByteArray(array);
        Assert.assertEquals(1 + 2 + 3, v0.write(buffer, 1));
        DbByteArray v1 = (DbByteArray) DbValue.read(buffer, 1);
        Assert.assertArrayEquals(array, v1.getByteArray());
    }
}
