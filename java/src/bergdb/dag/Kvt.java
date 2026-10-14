package bergdb.dag;

/**
 * An object of this class stores a key-value-time-spos tuple.
 */
public class Kvt {
    //
    // Suitable for for db internally.
    //
    
    public long[] key;
    public byte[] value;
    public long time;       // Time of the key node entry; not the write time (see GetData.kvTime).
    
    /**
     * Stream position of ValueNode.
     */
    public long spos;
    
    public String toString() {
        return "kvt:" + Keys.toDisplayString(Keys.toBytes(key));
    }
}
