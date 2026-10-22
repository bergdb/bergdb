package bergdb.pub;

/**
 * Transaction environment for a read-write transaction (rw-transaction).
 * The action of an rw-transaction uses this environment to get/set database key-value entries,
 * and to set the outputs of the transaction: its results for the caller.
 * The environment is valid only while Action.run() runs; a call to it after that
 * throws IllegalStateException.
 * 
 * @author Frans Lundberg
 */
public interface RwEnvironment extends ReadInterface {
    
    /**
     * @see Connection#get(String, Class)
     */
    public <TYPE> TYPE get(String key, Class<TYPE> clazz);
    
    /**
     * Deletes a database entry if it exists, otherwise, this method does nothing.
     * 
     * @param key Key of the database entry to delete.
     * @throws IllegalArgumentException if 'key' is null or otherwise of an invalid format.
     */
    public void delete(String key);
    
    /**
     * Stores an object using the 'key' field as the database key.
     * 
     * @param object The object to store in the database.
     * @throws MissingKeyFieldException
     * @throws IllegalArgumentException if key field is null or otherwise of an invalid format.
     * @throws IllegalArgumentException if 'object' is null.
     */
    public void put(Object object) throws MissingKeyFieldException;
    
    /**
     * @see WBuilder#put(String, Object)
     * @throws IllegalArgumentException if 'key' is null or otherwise of an invalid format.
     * @throws IllegalArgumentException if 'object' is null.
     */
    public void put(String key, Object object);
    
    /**
     * Sets an output of the transaction: a result for the caller of Connection.rw(),
     * who gets it with Transaction.getOutput() once the transaction has committed.
     * Outputs live in memory only; they are not stored. If the action is run again,
     * the outputs of the earlier run are cleared first, so the caller gets those of
     * the run that committed. Setting a name again replaces its value.
     * 
     * @param name The name of the output.
     * @param value The value of the output.
     * @throws IllegalArgumentException if name is null or empty, or if value is null.
     */
    public void setOutput(String name, Object value);
}

/*

Log
===

261022 setOutput(): its rules in the Javadoc. Transaction.getOutput() is typed and returns null
       for a missing output, and the environment refuses calls after Action.run() (bergdb 005-12).
130530 Frans: Added setOutput(). It *is* needed. Makes code less ugly.
130416 Frans: Renamed class to RwEnvironment.
130416 Frans: The method setOutput() was removed. I was in doubt, so I left it out.

*/