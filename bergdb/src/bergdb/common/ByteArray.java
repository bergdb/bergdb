package bergdb.common;

import java.util.Arrays;

/**
 * Wraps a byte[] and adds equals() and compareTo() implementations.
 * Useful when using a byte array as a hash map key.
 * 
 * @author Frans Lundberg
 */
public class ByteArray {
    private final byte[] array;
    
    public ByteArray(byte[] array) {
        if (array == null) {
            throw new IllegalArgumentException("array == null not allowed");
        }
        this.array = array;
    }
    
    public boolean equals(Object other) {
        if (!(other instanceof ByteArray)) {
            return false;
        }
        return Arrays.equals(array, ((ByteArray)other).array);
    }

    public int hashCode() {
        return Arrays.hashCode(array);
    }
}
