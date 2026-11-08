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
     * Gets the object stored under the key, created from 'clazz', or null if no entry
     * exists for the key.
     *
     * <p>Experimental in 2026.3 for a class other than String and byte[], with known
     * faults; such a get may change in a later release (bergdb 018-01, D6).</p>
     *
     * <p>A byte[] returned (by byte[].class, or by Object.class at a value of bytes) is
     * the database's own array, not a copy: do not change it. A change of it changes
     * what later reads return, in every connection, until the value leaves memory or
     * the database restarts, while the stream keeps the committed bytes. To change
     * the bytes, copy them first, with clone() (bergdb 015-47).</p>
     *
     * <p>The action's reads read one state, the latest as of its first read: they do not
     * see the transaction's own puts and deletes (bergdb 018-04, Q1).</p>
     *
     * @see Connection#get(String, Class)
     */
    public <TYPE> TYPE get(String key, Class<TYPE> clazz);
    
    /**
     * Checks whether an entry exists for the key, in the state that get() reads: the
     * transaction's own puts and deletes are not seen (bergdb 018-04, Q1).
     *
     * @throws IllegalArgumentException
     *             If key does not follow the allowed format, or is null, as for get()
     *             (bergdb 019-05).
     */
    public boolean exists(String key);
    
    /**
     * Deletes a database entry if it exists, otherwise, this method does nothing.
     * 
     * @param key Key of the database entry to delete.
     * @throws IllegalArgumentException if 'key' is null or otherwise of an invalid format.
     */
    public void delete(String key);
    
    /**
     * Sets the key-value entry with the given key to the provided object. A byte[] is
     * copied at the put: the caller may change or reuse its array afterwards.
     *
     * <p>Experimental in 2026.3 for an object that is neither a String nor a byte[], with
     * known faults; such a put may change in a later release (bergdb 018-01, D6).</p>
     *
     * <p>A String, and each string in an object, is Unicode text, stored as well-formed
     * UTF-8, as for WBuilder.put() (the package's {@linkplain bergdb.pub##strings Strings}).</p>
     *
     * @see WBuilder#put(String, Object)
     * @throws IllegalArgumentException if 'key' is null or otherwise of an invalid format.
     * @throws IllegalArgumentException if 'object' is null, or if it is a String with a
     *             lone surrogate, or an object with a string that has one, as for
     *             WBuilder.put() (bergdb 019-44, 021-04).
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