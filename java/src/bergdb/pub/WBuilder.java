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
     * Adds a set operation to the write transaction. The operation sets the
     * specified key to the provided object. A String is stored as its UTF-8 bytes,
     * a byte[] as it is. A byte[] is copied at the put:
     * the caller may change or reuse its array afterwards.
     *
     * <p>A String, and each string in an object (a field's value, an array's element, a
     * field's name), is Unicode text, stored as well-formed UTF-8; one with a lone surrogate
     * is refused. The rule in full: the package's
     * {@linkplain bergdb.pub##strings Strings} (bergdb 021-04).</p>
     *
     * <p>Experimental in 2026.3 for an object that is neither a String nor a byte[], with
     * known faults; such a put may change in a later release (bergdb 018-01, D6).</p>
     * 
     * @throws IllegalArgumentException
     *             If 'key' is null or otherwise invalid, or if object is null; or if it
     *             is a String with a lone surrogate, a char of U+D800 to U+DFFF that is not
     *             part of a surrogate pair, as a key with one is (bergdb 019-44); or if it
     *             is an object with a string that has one, at any depth: the message names
     *             the field, and an array element's index (bergdb 021-04).
     */
    public WBuilder put(String key, Object object);
    
    /**
     * Adds an operation to the write transaction that sets a key-value entry to the database.
     * The key string is taken from the 'key' field of 'object'.
     *
     * <p>Experimental in 2026.3, with known faults; it may change in a later release
     * (bergdb 018-01, D6).</p>
     * 
     * <p>Each string in the object is Unicode text, stored as well-formed UTF-8, as for
     * put(String, Object) (the package's {@linkplain bergdb.pub##strings Strings}).</p>
     * 
     * @throws MissingKeyFieldException If 'object' does not have a String field named 'key'.
     * @throws IllegalArgumentException
     *             If 'key' is null or otherwise invalid, or if object is null; or if a
     *             string in the object has a lone surrogate, as for put(String, Object)
     *             (bergdb 021-04).
     */
    public WBuilder put(Object object);
    
    /** 
     * Executes the puts and deletes as one transaction, and returns it when it has
     * committed.
     * 
     * @throws bergdb.pub.util.DbFailedException
     *             If the database has failed, in this transaction or before: it then
     *             refuses every transaction and read until it is restarted. See
     *             Database.
     */
    public Transaction execute();
}
