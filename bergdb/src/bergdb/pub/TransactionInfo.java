package bergdb.pub;

import java.util.List;

public interface TransactionInfo {
    /** Transaction time. */
    public Time time();
    
    /** 
     * Returns a list of the KVs of the transaction.
     * Value == null is used to represent delete operations.
     */
    public List<Kv<byte[]>> kvs();
}
