package bergdb.pubimp;


import bergdb.common.Bytes;
import bergdb.common.StringUtil;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.util.BadFormatException;

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
    private String value;
    
    /**
     * A string value, or null.
     *
     * @throws IllegalArgumentException  If 'value' has a lone surrogate, a char of U+D800
     *      to U+DFFF that is not part of a surrogate pair: UTF-8 cannot hold it (bergdb
     *      021-04). It is a LoneSurrogateException, which DbObject.toDbObject() gives the
     *      field's path.
     */
    public DbString(String value) {
        super('s');
        if (value != null && PubKeys.hasLoneSurrogate(value)) {
            throw new LoneSurrogateException("string", "");
        }
        this.value = value;
    }
    
    /** A string read from UTF-8 bytes: their decoding has no lone surrogate, no check. */
    private DbString(String value, boolean read) {
        super('s');
        this.value = value;
    }
    
    /**
     * A string of an object, or a field's name, with a lone surrogate (bergdb 021-04). The
     * message names where it is, from the outermost object: a field's name, and an array
     * element's index, such as "inner.names[3]"; each object and array on the way out adds
     * its step with in().
     */
    static final class LoneSurrogateException extends IllegalArgumentException {
        private static final long serialVersionUID = 1L;
        private final String what;      // "string" or "field name"
        private final String path;      // "" where not known
        
        LoneSurrogateException(String what, String path) {
            super((path.isEmpty() ? "A " + what : "The " + what + " at '" + path + "'")
                    + " has a lone surrogate, a char of U+D800 to U+DFFF that is not part of "
                    + "a surrogate pair. BergDB stores every string as well-formed UTF-8, "
                    + "which cannot hold one (bergdb 021-04); store such data as a byte[] or "
                    + "a char[].");
            this.what = what;
            this.path = path;
        }
        
        /** The same, one step further out: a field's name, or "[i]" for an array element. */
        LoneSurrogateException in(String step) {
            String p = path.isEmpty() || path.startsWith("[") ? step + path : step + "." + path;
            return new LoneSurrogateException(what, p);
        }
    }
    
    public int getByteSize() {
        return value == null ? 4 : 4 + StringUtil.utf8Size(value);
    }
    
    public int write(byte[] b, int offset) {
        if (value == null) {
            Bytes.intToBytesLE(-1, b, offset);
            offset += 4;
        } else {
            byte[] stringBytes = StringUtil.toBytes(value);
            assert 4 + stringBytes.length == getByteSize() : stringBytes.length + ", " + getByteSize();
            Bytes.intToBytesLE(stringBytes.length, b, offset);
            offset += 4;
            System.arraycopy(stringBytes, 0, b, offset, stringBytes.length);
            offset += stringBytes.length;
        }
        return offset;
    }
    
    // Should we convert string to int, long, double? Could be done is string is parsable with Double.parseDouble(), Long.parseLong(), ...
    
    public String toStringValue() {
        return value;
    }
    
    public String toString() {
        return value;
    }
    
    public static DbString parse(byte[] buffer, int offset) {
        return new DbString(parseToString(buffer, offset), true);
    }
    
    public static String parseToString(byte[] buffer, int offset) {
        int size = Bytes.bytesToIntLE(buffer, offset);
        offset += 4;
        if (size == -1) {
            return null;
        }
        
        if (size < 0 || size > buffer.length - offset) {
            throw new BadFormatException("Bad string size, " + size + " (bergdb 021-07).");
        }
        
        byte[] stringBytes = new byte[size];
        System.arraycopy(buffer, offset, stringBytes, 0, size);
        String value = StringUtil.toString(stringBytes);
        return value;
    }
    
    // ----
    
    @Nano
    public static void test0() {
        Assert.assertEquals("abc", new DbString("abc").toStringValue());
        Assert.assertEquals("", new DbString("").toStringValue());
        Assert.assertNull(new DbString(null).toStringValue());
    }
    
    @Nano
    public static void testSerialize0() {
        byte[] bytes = new byte[100];
        String s = "abc";
        DbString d0 = new DbString(s);
        
        d0.write(bytes, 12);
        DbString d1 = DbString.parse(bytes, 12);
        
        Assert.assertEquals("abc", d1.toStringValue());
    }
    
    @Nano
    public static void testSerialize1() {
        byte[] bytes = new byte[10];
        
        DbString d0 = new DbString("");
        d0.write(bytes, 0);
        DbString d1 = DbString.parse(bytes, 0);
        Assert.assertEquals("", d1.toStringValue());
        
        d0 = new DbString(null);
        d0.write(bytes, 0);
        d1 = DbString.parse(bytes, 0);
        Assert.assertNull(d1.toStringValue());
    }
}
