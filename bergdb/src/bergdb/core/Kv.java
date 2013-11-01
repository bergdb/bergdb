package bergdb.core;

import bergdb.dag.Keys;

/**
 * A key-value pair. Designed for use with Trans.
 * 
 * @see Trans
 * @author Frans Lundberg
 */
public class Kv {
    public long[] keySegments;
    
    /** The value. null is used to indicate a delete operation. */
    public byte[] value;
    
    /** Key transformation, or null if none. */
    public KeyTransformation keyTransformation;
    
    /** Value transformation, or null if none. */
    public ValueTransformation valueTransformation;
    
    /**
     * The constructor does not copy arrays, just references.
     * Arrays must not be changed by caller after this constructor is called.
     */
    public Kv(byte[] key, byte[] bytes) {
        this.keySegments = Keys.toSegments(key);
        this.value = bytes;
    }
    
    /**
     * The constructor does not copy arrays, just references.
     * Arrays must not be changed by caller after this constructor is called.
     */
    public Kv(long[] keySegments, byte[] value) {
        this.keySegments = keySegments;
        this.value = value;
    }
}
