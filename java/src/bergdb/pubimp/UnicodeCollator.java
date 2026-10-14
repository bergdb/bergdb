package bergdb.pubimp;

import java.io.UnsupportedEncodingException;

/**
 * Sorts strings according to their Unicode code points.
 * 
 * @author Frans Lundberg
 */
public class UnicodeCollator implements KCollator {
    public static final UnicodeCollator INSTANCE = new UnicodeCollator();
    
    /** No need to create new instances. One is enough. */
    private UnicodeCollator() {}

    public final byte[] getSortBytes(String s) {
        //
        // The non-last bytes are never 0. This is technically important. ICU collation keys
        // never contain 0 either, except for the last byte that always is 0.
        // 2 is added to each UTF-8 byte. This is possible since valid UTF-8 bytes never have the
        // value 0xfe or 0xff.
        //
        // It would be possible to improve performance. Currently, there is double mem alloc.
        //
        assert s != null;
        byte[] bytes;
        try {
            bytes = s.getBytes("UTF-8");
        } catch (UnsupportedEncodingException e) {
            throw new Error("Never happens, UTF-8 must be supported be a valid JVM.");
        }
        final int bytesLength = bytes.length;
        for (int i = 0; i < bytesLength; i++) {
            byte b = bytes[i];
            if (b == (byte) 0xff) {
                throw new Error("Byte value 0xff should not exist in UTF-8 bytes, s = '" + s + "'.");
            }
            b++;
            b++;
            bytes[i] = b;
        }
        
        byte[] sortBytes = new byte[bytes.length + 1];
        System.arraycopy(bytes, 0, sortBytes, 0, bytes.length);
        return sortBytes;
    }
}
