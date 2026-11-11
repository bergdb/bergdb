package bergdb.core;

/**
 * A low-level class to store a key-value pair as part of 
 * a transaction specification. Designed for use with Trans.
 * 
 * @see Trans
 * @author Frans Lundberg
 */
public final class Kv {
    private long[] keySegments;
    
    /** The value, null is used to indicate a delete operation. */
    private byte[] value;
    
    /** Key transformation, or null if none. */
    public final KeyTransformation keyTransformation;
    
    /** Value transformation, or null if none. */
    public final ValueTransformation valueTransformation;
    
    /**
     * The number of the call that made this KV, in the order of its Trans.Builder's puts and
     * deletes, from 0; set by Trans.Builder.build(). Of the KVs of a transaction that key
     * transformations make one key, Db.putKvs keeps the one with the highest number: the
     * last operation wins (bergdb 024-10, section 3, R2).
     */
    int call;
    
    /**
     * The constructor does not copy arrays, just references.
     * Arrays must not be changed by caller after this constructor is called.
     */
    public Kv(long[] keySegments, byte[] value) {
        this(keySegments, value, null, null);
    }
    
    /**
     * Creates a Kv from key segment, the key, and keyTransformation (may be null)
     * and ValueTransformation (may be null).
     * The constructor does not copy arrays the arrays; 
     * they must not be modified after this constructor has been called.
     */
    public Kv(long[] keySegments, byte[] value, 
            KeyTransformation keyTransformation, ValueTransformation valueTransformation) {
        this.keySegments = keySegments;
        this.value = value;
        this.keyTransformation = keyTransformation;
        this.valueTransformation = valueTransformation;
    }
    
    public long[] getKey() {
        return keySegments;
    }
    
    public void setKey(long[] key) {
        keySegments = key;
    }
    
    public byte[] getValue() {
        return value;
    }
    
    public KeyTransformation getKeyTransformation() {
        return keyTransformation;
    }
    
    public void transformValue(long transTime, byte[] previousValue) {
        assert valueTransformation != null;
        value = valueTransformation.transform(transTime, value, previousValue);
    }
}
