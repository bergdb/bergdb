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
// 2026-10-13 (docs/problem.md Q9, docs/levels.md W3): the method time() was
// removed. The time it returned was not the time of the write: after a time split of a key
// node it was the time of the split, and reclaim rewrites live values in later transactions.
// An exact write time would be stored in the value node (a format change), not done.
