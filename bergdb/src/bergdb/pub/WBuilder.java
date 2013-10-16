package bergdb.pub;

/**
 * A builder used to build a write-only transaction.
 * 
 * @author Frans Lundberg
 */
public interface WBuilder {
    
    /**
     * Adds a delete operation to the write transaction. The operation deletes the database entry
     * with the given key if it exists, otherwise, the operation has no effect.
     */
    public WBuilder delete(String key);
    
    
    /**
     * Adds a set operation to the write transaction. The operation sets the specified
     * key to the provided object. Special handling is provided for object of type byte[] 
     * and java.lang.String.
     * 
     * @throws IllegalArgumentException
     */
    public WBuilder put(String key, Object object);
    
    /**
     * Adds an operation to the write transaction that sets a key-value entry to the database.
     * The key string is taken from the 'key' field of 'object'.
     * 
     * @throws MissingKeyFieldException If 'object' does not have a String field named 'key'.
     */
    public WBuilder put(Object object);
    
    /**
     * Creates and returns the transaction.
     */
    public Transaction build();
    
    /** 
     * Shortcut for <code>build().execute()</code>.
     */
    public Transaction execute();
}

/*

This is really a convenience for the user. We could have used an RwTransaction too,
I suppose.

*/