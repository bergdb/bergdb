package bergdb.pub;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pubimp.ObjectFormat;

/**
 * A value of bytes, any bytes, of any length up to a stored value's limit: the type char
 * 'b', DbObject.BYTE_ARRAY; stored as Binson's bytes (bergdb 020-07). Immutable: the
 * constructor copies the bytes, and getByteArray() gives a copy.
 * 
 * @author Frans Lundberg
 */
public final class DbByteArray extends DbValue {
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
        ObjectFormat.checkValueSize(5L + value.length);       // bergdb 020-07, R15
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
    
    /**
     * The bytes, a new array: a change of it does not change this value (2026-11-09, bergdb
     * 020-10, B3: the value's own array, so a DbByteArray could change).
     *
     * @return A copy of the bytes.
     */
    public byte[] getByteArray() {
        return value.clone();
    }
    
    public int write(byte[] b, int offset) {
        offset = ObjectFormat.writeBytesHead(b, offset, value.length);
        System.arraycopy(value, 0, b, offset, value.length);
        return offset + value.length;
    }
    
    // ---- Tests ----
    
    @Nano
    private static void test0() {
        Assert.assertArrayEquals(new byte[]{1, 2, 3}, 
                new DbByteArray(new byte[]{1, 2, 3}).getByteArray());
    }
    
    @Nano
    private static void testSerialize() {
        byte[] buffer = new byte[100];
        byte[] array = new byte[] {1, 2, -3};
        DbByteArray v0 = new DbByteArray(array);
        Assert.assertEquals(1 + 2 + 3, v0.write(buffer, 1));
        DbByteArray v1 = (DbByteArray) DbValue.read(buffer, 1);
        Assert.assertArrayEquals(array, v1.getByteArray());
    }
    
    /** Immutable (bergdb 020-10, B3): getByteArray() gives a copy, as the API says. */
    @Nano
    private static void testImmutable() {
        DbByteArray v = new DbByteArray(new byte[] {1, 2, 3});
        v.getByteArray()[0] = 9;
        Assert.assertArrayEquals(new byte[] {1, 2, 3}, v.getByteArray());
        byte[] b = new byte[10];
        Assert.assertEquals(5, v.write(b, 0));
        Assert.assertEquals(1, b[2]);
    }
}
