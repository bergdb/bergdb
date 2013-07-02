package bergdb.pubimp;

import bergdb.common.BadFormatException;
import bergdb.common.Bytes;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;

/**
 * The DbObject type for a byte array.
 * The type char for this type is 'b'.
 * 
 * @author Frans Lundberg
 */
public class DbByteArray extends DbValue {
    private byte[] value;
    
    public DbByteArray(byte[] value) {
        super('b');
        this.value = value;
    }
    
    public int getByteSize() {
        return value == null ? 4 : 4 + value.length;
    }
    
    public String toString() {
        return value == null ? "b:null" : "b:" + value.length;
    }
    
    public byte[] getByteArray() {
        return value;
    }
    
    public int write(byte[] b, int offset) {
        if (value == null) {
            Bytes.intToBytesLE(-1, b, offset);
            offset += 4;
        } else {
            Bytes.intToBytesLE(value.length, b, offset);
            offset += 4;
            System.arraycopy(value, 0, b, offset, value.length);
            offset += value.length;
        }
        return offset;
    }
    
    @SuppressWarnings("unchecked")
    public <TYPE> TYPE toJavaObject(Class<TYPE> c, ClassToObject c2o) {
        // Converts only to byte[].class. Conversions to short[] and so on usually does not
        // make sense. Consider for example the bytes of a JPEG image. Byte array often does
        // not store a number of integers with integer semantics.
        
        Object result;
        
        if (c.equals(byte[].class)) {
            result = value == null ? null : value.clone();
        } else {
            result = null;
        }
        return (TYPE) result;
    }
    
    public static DbByteArray parse(byte[] buffer, int offset) {
        return new DbByteArray(parseToByteArray(buffer, offset));
    }
    
    public static byte[] parseToByteArray(byte[] buffer, int offset) {
        int size = Bytes.bytesToIntLE(buffer, offset);
        offset += 4;
        if (size == -1) {
            return null;
        }
        
        if (size < 0) {
            throw new BadFormatException("Bad byte array size, " + size + ".");
        }
        
        byte[] value = new byte[size];
        System.arraycopy(buffer, offset, value, 0, size);
        return value;
    }
    
    // ---- Tests ----
    
    @T
    public static void test0() {
        Assert.assertArrayEquals(new byte[]{1, 2, 3}, 
                new DbByteArray(new byte[]{1, 2, 3}).getByteArray());
    }
    
    @T
    public static void testSerialize() {
        byte[] buffer = new byte[100];
        byte[] array = new byte[] {1, 2, -3};
        DbByteArray v0 = new DbByteArray(array);
        v0.write(buffer, 1);
        DbByteArray v1 = DbByteArray.parse(buffer, 1);
        Assert.assertArrayEquals(array, v1.getByteArray());
    }
}
