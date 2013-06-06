package kissdb.pub;

/**
 * Transaction environment for a read-write transaction (rw-transaction).
 * The action of an rw-transaction uses this environment to get/set database key-value entries.
 * 
 * @author Frans Lundberg
 */
public interface RwEnvironment extends ReadInterface {
    
    /**
     * Returns true if a value exists for the given key.
     */
    public boolean exists(String key);

    /**
     * @see Connection#get(String, Class)
     */
    public <TYPE> TYPE get(String key, Class<TYPE> clazz);
    
    /**
     * Deletes a database entry if it exists, otherwise, this method does nothing.
     * 
     * @param key Key of the database entry to delete.
     */
    public void delete(String key);
    
    /**
     * Stores an object using the 'key' field as the database key.
     * 
     * @param object The object to store in the database.
     * @throws MissingKeyFieldException
     */
    public void set(Object object) throws MissingKeyFieldException;
    
    /**
     * @see WBuilder#set(String, Object)
     */
    public void set(String key, Object object);
    
    /**
     * Sets an output value for a transaction; the output object is available 
     * through the method Transaction.getOutput(String).
     * 
     * @param name The name of the output value.
     * @param value The value object.
     */
    public void setOutput(String name, Object value);
}

/*

Log
===

130530 Frans: Added setOutput(). It *is* needed. Makes code less ugly.
130416 Frans: Renamed class to RwEnvironment.
130416 Frans: The method setOutput() was removed. I was in doubt, so I left it out.

*/