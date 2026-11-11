package bergdb.core;

/**
 * Transformation for a key applied after transTime is known.
 * 
 * @author Frans Lundberg
 */
public interface KeyTransformation {
    
    /**
     * This method is allowed to modify trans.kvs[index].key and trans.writeKeyHashes[index],
     * and allowed to read trans.transTime. 
     * Other data should not be read or modified.
     * The implementation of this method must not throw any exception. It runs after the
     * transaction's go point, in Db.putKvs(); an exception there fails the database
     * (bergdb 005-01). The new key is not size-checked: Db.checkSize, before the go point,
     * counts the key before the transformation (bergdb 015-51; ValueTransformation).
     * Db.putKvs runs every key transformation of the transaction first, then sorts the KVs
     * by their keys and puts them in that order (bergdb 023-08, section 7, Q4); of the KVs
     * that have the same key then, it puts one, the one called last in the builder (bergdb
     * 024-10, section 3, R2).
     * 
     * @param trans The transaction for which to modify the key.
     * @param index The index to the KV pair of the transaction.
     */
    public void transform(Trans trans, int index);
}
