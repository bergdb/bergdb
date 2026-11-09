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
     * Returns the value.
     */
    public TYPE value();
}

// 1410 Frans: ikey() should probably be hidden from Pub API. Maybe two interface CoreKv and Kv.
//      Core Layer user could cast to CoreKv interface. CoreKv would have more information.
// 2026-11-09 (bergdb 020-10, section 7, step B2): ikey() removed, as no caller used it and it
// was not for the Pub API's user; transactionInfo()'s Kvs threw UnsupportedOperationException.
// 2026-10-13 (bergdb 011-01 Q9, bergdb 011-04 W3): the method time() was
// removed. The time it returned was not the time of the write: after a time split of a key
// node it was the time of the split, and reclaim rewrites live values in later transactions.
// An exact write time would be stored in the value node (a format change), not done.
