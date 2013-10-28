package bergdb.pub;

/**
 * Represents a database transaction, either a w-transaction (write transaction) or an
 * rw-transaction (read-write transaction).
 * 
 * @author Frans Lundberg
 */
public interface Transaction {

    /**
     * Executes the transaction in the database.
     * 
     * @return Transaction  This Transaction is returned as a convenience
     * when a builder is used to create a Transaction and execute it.
     * @throws DbException  If the transaction could not be processed because the database 
     * is faulty.
     */
    //
    // Throws StreamIOException, StreamFormatException, InternalDataException
    // Possibly document as simply DBException.
    //
    public Transaction execute();

    /**
     * Returns an output object that the transaction created.
     */
    public Object getOutput(String name);
    
    /**
     * Waits until ordinary durability has been attained for the transaction.
     * 
     * @throws DbException
     */
    public void sync();
    
    /**
     * Wait until strong durability has been attained for the transaction.
     * 
     * @throws DbException
     */
    public void syncStrong();
}
