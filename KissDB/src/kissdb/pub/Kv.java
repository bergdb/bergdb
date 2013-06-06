package kissdb.pub;

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

// 1304 Frans: Note, method "public long time()" could be added if/when needed.
// Consider reclaim rewrites properly first.
