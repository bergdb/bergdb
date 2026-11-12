package bergdb.core;

/**
 * Transformation for a key applied after transTime is known.
 * 
 * @author Frans Lundberg
 */
public interface KeyTransformation {
    
    /**
     * This method is allowed to change the key of trans.kvs[index] (Kv.setKey()) and
     * trans.writeKeyHashes[index], and allowed to read trans.tt, the transaction's time.
     * Other data should not be read or modified.
     * The implementation of this method must not throw any exception. It runs under the
     * write lock, at the transaction's time, in Db.transformKeys(); an exception there fails
     * the database (bergdb 005-01), as when it ran after the go point, in Db.putKvs() (until
     * bergdb 024-16). The new key is checked after the transformations: a key of more than
     * Db.MAX_KEY_BYTES bytes (111, L2), or keys of the transaction of more than
     * Db.MAX_TRANS_KEY_BYTES (L3), refuse the transaction with a DbException, nothing of it
     * written, and the database goes on (Db, "Limits"; bergdb 024-24; until 024-24 the new
     * key was not checked, bergdb 015-51). Db.transformKeys runs every key
     * transformation of the transaction first, then sorts the KVs by their keys, and
     * Db.putKvs puts them in that order (bergdb 023-08, section 7, Q4). If two KVs have the
     * same key then, the transaction is refused with a DbException before its go point, and
     * each transformed KV gets its key as written and its write hash back (bergdb 024-16):
     * a transaction has one operation a key.
     * 
     * @param trans The transaction for which to modify the key.
     * @param index The index to the KV pair of the transaction.
     */
    public void transform(Trans trans, int index);
}
