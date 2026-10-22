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
     * Returns the output that the action of the transaction set with the given name
     * in the run that committed (RwEnvironment.setOutput()), or null if it set none.
     * A w-transaction has no action and no outputs: null for every name.
     * 
     * @param name The name of the output.
     * @param clazz The class of the output, or a superclass of it (Long.class for a long,
     *            which setOutput() gets boxed).
     * @throws IllegalArgumentException if name is null or empty, or if clazz is null.
     * @throws ClassCastException if the output is not an instance of clazz.
     */
    public <TYPE> TYPE getOutput(String name, Class<TYPE> clazz);
    
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
    
    // TODO LATER. Idea, 2026-10-13 (Frans): isDurable() and 
    // isDurable(SyncLevel), returning at once whether this transaction has 
    // attained the sync level. A non-blocking companion to sync(): commit 
    // now, ask later. Cheap to implement: StorageManager already tracks the 
    // durable stream length per level (d1Size, d2Size); compare with the 
    // transaction's last position. Same idea in Connection.
}
