package bergdb.pub;

/**
 * An immutable key-value pair.
 * 
 * @author Frans Lundberg
 */
public interface Kv<TYPE> {
    /**
     * Returns the key.
     */
    public String key();
    
    /**
     * Used internally, not intended for the Pub API user.
     */
    public String ikey();
    
    /**
     * Returns the value.
     */
    public TYPE value();
}

// 1410 Frans: ikey() should probably be hidden from Pub API. Maybe two interface CoreKv and Kv.
//      Core Layer user could cast to CoreKv interface. CoreKv would have more information.
// 1304 Frans: Note, method "public long time()" could be added if/when needed.
// Consider reclaim rewrites properly first.
