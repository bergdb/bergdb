package bergdb.pub;

import bergdb.core.SyncLevel;
import bergdb.pub.util.DbException;

/**
 * <p>Represents a database transaction that has been executed.
 * The transaction can be a w-transaction (write transaction) or an
 * rw-transaction (read-write transaction).
 * A database read operation is not represented by an object of this interface.</p>
 * 
 * <p>To allow Connection and Database objects to be garbage collected, 
 * do not keep references to Transaction:s for a long time.</p>
 * 
 * @author Frans Lundberg
 */
public interface Transaction {

    /**
     * Returns an output object that the transaction created.
     */
    public Object getOutput(String name);
    
    /**
     * Returns the transaction timestamp of the transaction; 
     * the time when it was actually executed.
     * The timestamp is unique among all transactions executed by the database.
     */
    public Time getTime();
    
    /**
     * Waits until ordinary durability has been attained for this transaction.
     * 
     * @throws DbException
     */
    public void sync();
    
    /** 
     * Waits until the specific sync level has been attained for this transaction.
     * 
     * @throws DbException
     */
    public void sync(SyncLevel syncLevel);
}
