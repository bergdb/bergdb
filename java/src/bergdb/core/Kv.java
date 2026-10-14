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
    
    public boolean hasKeyTransformation() {
        return keyTransformation != null;
    }
    
    public boolean hasValueTransformation() {
        return value != null;
    }
    
    public KeyTransformation getKeyTransformation() {
        return keyTransformation;
    }
    
    public void transformValue(long transTime, byte[] previousValue) {
        assert valueTransformation != null;
        value = valueTransformation.transform(transTime, value, previousValue);
    }
}
