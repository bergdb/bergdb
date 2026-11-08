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
     *             the field, and an array element's index (bergdb 021-04). Or if the object
     *             cannot be stored exactly (the package's
     *             {@linkplain bergdb.pub##objects Objects}; bergdb 020-09): its class, or a
     *             class it reaches, is not a Data Object class; an array in it has a null
     *             element; a value's class is not its field's type; it has a reference
     *             cycle, or is nested deeper than 16 levels of objects and arrays; or it is
     *             larger than a stored value may be. The message names the class or the
     *             place. A null field is not refused: it is left out, absent.
     */
    public WBuilder put(String key, Object object);
    
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
