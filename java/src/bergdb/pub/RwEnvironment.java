package bergdb.pub;

/**
 * Transaction environment for a read-write transaction (rw-transaction).
 * The action of an rw-transaction uses this environment to get/set database key-value entries,
 * and to set the outputs of the transaction: its results for the caller.
 * The environment is valid only while Action.run() runs; a call to it after that
 * throws IllegalStateException.
 * Of several puts and deletes of one key in the action, the last one counts, as in a
 * WBuilder (bergdb 015-40, 020-25).
 *
 * <p>Threads (bergdb 021-21). The action may use the environment from several threads
 * while it runs, such as a parallel stream over keys, or a task that it hands the
 * environment to and waits for. Their reads and writes are taken one at a time: each read
 * is at the transaction's read time and in its read set, each put and delete is in the
 * transaction, and of several of one key the last one taken counts. The environment is closed when the
 * action returns or throws, before the commit, for every thread: a call after that, or one
 * that has not made its change by then, throws IllegalStateException and changes nothing,
 * so the action should wait for its threads before it returns. Each run of the action has
 * an environment of its own: one kept from an earlier run stays closed.</p>
 * 
 * @author Frans Lundberg
 */
public interface RwEnvironment extends ReadInterface {
    
    /**
     * Gets the object stored under the key, created from 'clazz', or null if no entry
     * exists for the key.
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
     * <p>A class other than String, byte[], DbObject and Object is a Data Object class, or a
     * primitive, its wrapper or an array class for a value put as one, and the stored object
     * is converted to it as by Connection.get() (bergdb 020-09).</p>
     *
     * @throws ObjectCreationException  As Connection.get(): the action's exception, which
     *             ends the action; the database goes on.
     * @throws DataFormatException  As Connection.get(), for a value read as a String that
     *             is not well-formed UTF-8; as ObjectCreationException, the action's
     *             exception (bergdb 021-06).
     * @throws IllegalArgumentException  If key does not follow the allowed format, or is
     *             null, or if clazz is null, as for Connection.get() (bergdb 020-25).
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
     * <p>A String, and each string in an object, is Unicode text, stored as well-formed
     * UTF-8, as for WBuilder.put() (the package's {@linkplain bergdb.pub##strings Strings}).</p>
     *
     * <p>An object, a value that is neither a String nor a byte[], is put only at an object
     * key, one without a suffix or with ".obj"; at a key with another suffix the put throws
     * IllegalArgumentException, as for WBuilder.put() (the package's
     * {@linkplain bergdb.pub##objects Objects}).</p>
     *
     * <p>With key replace on, as the connection had it at rw(), each "${transactionTime}" in
     * the key is replaced by the transaction's time, the time of the run that commits
     * (Connection.setEnableKeyReplace(); bergdb 020-24-02, I-6).</p>
     *
     * @see WBuilder#put(String, Object)
     * @throws IllegalArgumentException if 'key' is null or otherwise of an invalid format.
     * @throws IllegalArgumentException if 'object' is null, or if it is a String with a
     *             lone surrogate or too long, or an object with a string that has one, as
     *             for WBuilder.put() (bergdb 019-44, 021-04; 020-08, section 3); or if the
     *             object cannot be stored exactly, as for WBuilder.put() (bergdb 020-09).
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