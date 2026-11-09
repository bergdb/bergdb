package bergdb.pub;

import java.util.List;

/**
 * Information about a transaction: its time and its KVs. Returned by
 * Connection.transactionInfo() for the transaction that wrote the last value
 * retrieved with get().
 */
public interface TransactionInfo {
    /** Transaction time. */
    public Time time();
    
    /** 
     * Returns a list of the KVs of the transaction: the user's puts and deletes.
     * A delete of a key that had no entry is left out, as it writes nothing (bergdb
     * 018-04, Q4).
     * The KVs that the database writes itself, the entries of an index, are
     * left out, and so are those at a key that is no key of the Pub API, which
     * only a write through the Core's Db makes (bergdb 020-22).
     * Value == null is used to represent delete operations.
     */
    public List<Kv<byte[]>> kvs();
}
