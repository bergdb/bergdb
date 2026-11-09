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
    /**
     * The time of the key node entry that points to the value: not the time of the write,
     * but at or after it and at or before the lookup time, as GetData.kvTime says (bergdb
     * 021-19). For the time of the write: a getOne() of the key at the scan's
     * GetMany.actualLookupTime gives the position of the value's transaction, GetData.tpos,
     * and Db.getTrans(tpos).tt its time.
     */
    public long time;
    
    /**
     * Stream position of ValueNode.
     */
    public long spos;
    
    public String toString() {
        return "kvt:" + Keys.toDisplayString(Keys.toBytes(key));
    }
}
