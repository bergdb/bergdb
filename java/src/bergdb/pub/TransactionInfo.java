package bergdb.pub;

import java.util.List;

public interface TransactionInfo {
    /** Transaction time. */
    public Time time();
    
    /** 
     * Returns a list of the KVs of the transaction: the user's puts and deletes.
     * The KVs that the database writes itself, the entries of an index, are
     * left out.
     * Value == null is used to represent delete operations.
     */
    public List<Kv<byte[]>> kvs();
}
