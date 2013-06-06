package kissdb.core;

/**
 * The STM approach requires a set of key hashes to be stored to determine whether read keys
 * have been modified after they were read.
 */
public interface IKeyModSet {
    /**
     * Returns true if a key with hash 'keyHash' has been modified by a transaction with a 
     * transactionTime strictly greater than 'time'.
     * The method also returns true if 'time' is too old, so there is no information about the
     * key hash.
     */
    public abstract boolean modifiedAfter(long time, long keyHash);

    /**
     * Adds a time-hash pair to the set of key hashes.
     */
    public abstract void add(long time, long keyHash);
}
