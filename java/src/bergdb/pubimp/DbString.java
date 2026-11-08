package bergdb.pubimp;


import java.nio.charset.StandardCharsets;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * The DbObject type for a string stored in UTF-8 format.
 * The type char for this type is 's'.
 *
 * <p>A string is Unicode text, stored as well-formed UTF-8 (RFC 3629), as every string
 * BergDB stores: one with a lone surrogate is refused (bergdb 021-04; the Pub API's package
 * bergdb.pub, "Strings").</p>
 * 
 * @author Frans Lundberg
 */
public class DbString extends DbValue {
    private final String value;
    private byte[] utf8;        // its UTF-8, made once when written
    
    /**
     * A string value.
     *
     * @throws IllegalArgumentException  If 'value' is null: BergDB stores no null, a field
     *      without a value is left out (bergdb 020-04). If 'value' has a lone surrogate, a
     *      char of U+D800 to U+DFFF that is not part of a surrogate pair: UTF-8 cannot hold it
     *      (bergdb 021-04); then it is a DbValue.PathException, which DbObject.toDbObject()
     *      gives the field's path.
     */
    public DbString(String value) {
        super('s');
        if (value == null) {
            throw new IllegalArgumentException("value == null not allowed: BergDB stores no "
                    + "null, leave the field out (bergdb 020-04, section 2.4)");
        }
        if (PubKeys.hasLoneSurrogate(value)) {
            throw PathException.loneSurrogate("string");
        }
        this.value = value;
    }
    
    /** A string read from well-formed UTF-8: its decoding has no lone surrogate, no check. */
    private DbString(String value, boolean read) {
        super('s');
        this.value = value;
    }
    
    /** The string at 'p' of checked bytes (bergdb 020-07, R11). */
    static DbString read(byte[] b, int p) {
        return new DbString(ObjectFormat.stringAt(b, p), true);
    }
    
    private byte[] utf8() {
        byte[] u = utf8;
        if (u == null) {
            u = value.getBytes(StandardCharsets.UTF_8);
            utf8 = u;
        }
        return u;
    }
    
    public int getByteSize() {
        int length = utf8().length;
        return ObjectFormat.lengthSize(length) + length;
    }
    
    public int write(byte[] b, int offset) {
        byte[] u = utf8();
        offset = ObjectFormat.writeStringHead(b, offset, u.length);
        System.arraycopy(u, 0, b, offset, u.length);
        return offset + u.length;
    }
    
    // Should we convert string to int, long, double? Could be done is string is parsable with Double.parseDouble(), Long.parseLong(), ...
    
    public String toStringValue() {
        return value;
    }
    
    public String toString() {
        return value;
    }
    
    // ----
    
    @Nano
    public static void test0() {
        Assert.assertEquals("abc", new DbString("abc").toStringValue());
        Assert.assertEquals("", new DbString("").toStringValue());
        try {
            new DbString(null);
            throw new AssertionError("no exception");
        } catch (IllegalArgumentException e) {
            // Expected: no null (bergdb 020-04).
        }
    }
    
    @Nano
    public static void testSerialize0() {
        byte[] bytes = new byte[100];
        String s = "abc";
        DbString d0 = new DbString(s);
        
        Assert.assertEquals(12 + 2 + 3, d0.write(bytes, 12));
        DbString d1 = (DbString) DbValue.read(bytes, 12);
        
        Assert.assertEquals("abc", d1.toStringValue());
    }
    
    @Nano
    public static void testSerialize1() {
        byte[] bytes = new byte[10];
        
        DbString d0 = new DbString("");
        Assert.assertEquals(2, d0.write(bytes, 0));
        DbString d1 = (DbString) DbValue.read(bytes, 0);
        Assert.assertEquals("", d1.toStringValue());
        
        String s = "\u00e9".repeat(64);      // 128 bytes: the length in 2 bytes
        bytes = new byte[200];
        Assert.assertEquals(3 + 128, new DbString(s).getByteSize());
        Assert.assertEquals(3 + 128, new DbString(s).write(bytes, 0));
        Assert.assertEquals(s, ((DbString) DbValue.read(bytes, 0)).toStringValue());
    }
}
