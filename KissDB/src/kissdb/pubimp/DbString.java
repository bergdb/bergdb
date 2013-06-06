package kissdb.pubimp;

import java.nio.ByteBuffer;

import kissdb.common.Bytes;
import kissdb.common.Util;
import kissdb.nanotest.Assert;
import kissdb.nanotest.T;

/**
 * The DbObject type for a string stored in UTF-8 format.
 * The type char for this type is 's'.
 * 
 * @author Frans Lundberg
 */
public class DbString extends DbValue {
    private String value;
    
    public DbString(String value) {
        super('s');
        this.value = value;
    }
    
    public int getByteSize() {
        return value == null ? 4 : 4 + Util.utf8Size(value);
    }
    
    public void write(ByteBuffer b) {
        if (value == null) {
            b.putInt(-1);
        } else {
            byte[] stringBytes = Util.toBytes(value);
            int size = stringBytes.length;
            assert size == getByteSize() : size + " != " + getByteSize();
            b.putInt(size);
            b.put(stringBytes, 0, stringBytes.length);
        }
    }
    
    public int write(byte[] b, int offset) {
        if (value == null) {
            Bytes.intToBytesLE(-1, b, offset);
            offset += 4;
        } else {
            byte[] stringBytes = Util.toBytes(value);
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
        return new DbString(parseToString(buffer, offset));
    }
    
    public static String parseToString(byte[] buffer, int offset) {
        int size = Bytes.bytesToIntLE(buffer, offset);
        offset += 4;
        if (size == -1) {
            return null;
        }
        
        byte[] stringBytes = new byte[size];
        System.arraycopy(buffer, offset, stringBytes, 0, size);
        String value = Util.toString(stringBytes);
        return value;
    }
    
    // ----
    
    @T
    public static void test0() {
        Assert.assertEquals("abc", new DbString("abc").toStringValue());
        Assert.assertEquals("", new DbString("").toStringValue());
        Assert.assertNull(new DbString(null).toStringValue());
    }
    
    @T
    public static void testSerialize0() {
        byte[] bytes = new byte[100];
        String s = "abc";
        DbString d0 = new DbString(s);
        
        d0.write(bytes, 12);
        DbString d1 = DbString.parse(bytes, 12);
        
        Assert.assertEquals("abc", d1.toStringValue());
    }
    
    @T
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
