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
     * (bergdb 005-01).
     * 
     * @param trans The transaction for which to modify the key.
     * @param index The index to the KV pair of the transaction.
     */
    public void transform(Trans trans, int index);
}
