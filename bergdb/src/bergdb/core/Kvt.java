package bergdb.core;

/**
 * An object of this class stores a key-value-time-spos tuple.
 */
public class Kvt {
    //
    // Suitable for for db internally.
    //
    
    public long[] key;
    public byte[] value;
    public long time;
    
    /**
     * Stream position of ValueNode.
     */
    public long spos;
}
