package bergdb.dag;

/**
 * An object of this class stores a key-value-time-spos tuple. A getMany() gives one for each
 * KV (GetMany.result): key, the key as segments, whose bytes Keys.toBytes() gives; value, the
 * value, the database's own array while it is in memory, which the caller must not change;
 * spos, the stream position of the value node (bergdb 020-24-09, U9-8).
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
