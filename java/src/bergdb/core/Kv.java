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
     * BergDB's own KV, put by Trans.Builder's internal calls (putLongKey(), deleteLongKey()):
     * its key may be longer than Db.MAX_KEY_BYTES (bergdb 024-17, L2), also after a key
     * transformation (Db.transformKeys).
     */
    boolean longKey;
    
    /**
     * Put or deleted by Trans.Builder's Core calls (putCore(), deleteCore()): its key may be
     * one that the Core writes itself (Trans.coreKey()), which Db.execute() refuses for any
     * other KV of a transaction that is not reclaim's (bergdb 024-37; 010-04, R5).
     */
    boolean coreWrite;
    
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
    
    /**
     * Sets the value back to the one given, after transformValue(), when Db.execute() refuses
     * the transaction before its go point (Db.giveBack; bergdb 026-06).
     */
    void setValue(byte[] value) {
        this.value = value;
    }
}
