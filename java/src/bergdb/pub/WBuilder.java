package bergdb.pub;

/**
 * A builder used to build a write-only transaction. Get one with Connection.w(), add the
 * transaction's puts and deletes, and execute() it once:
 *
 * <pre>
 *     c.w().put("/a.txt", "a").delete("/b.txt").execute();
 * </pre>
 *
 * <p>Of several puts and deletes of one key, the last one counts: a put after a delete
 * puts, a delete after a put deletes (bergdb 015-40, 020-25).</p>
 *
 * <p>execute() spends the builder, whatever it threw: a later put(), delete() or execute()
 * throws IllegalStateException (bergdb 020-21, 2). For another transaction, get a new
 * builder.</p>
 *
 * <p>A builder is for one thread, as its Connection (Connection, "Threads"). One that
 * threads share anyway takes their calls one at a time: each put() and delete() made
 * before execute() is in the transaction, and one after it, also one that waited for it,
 * throws IllegalStateException (bergdb 021-22). execute() is a call of the connection: it
 * throws IllegalStateException, and leaves the builder unspent, while another thread is in
 * a call of the connection.</p>
 * 
 * @author Frans Lundberg
 */
public interface WBuilder {
    
    /**
     * Adds a delete operation to the write transaction. The operation deletes the database entry
     * with the given key if it exists, otherwise, the operation has no effect.
     *
     * @throws IllegalArgumentException  If 'key' is null or otherwise invalid.
     * @throws IllegalStateException  If execute() was called: the builder is spent.
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
     * <p>An object, a value that is neither a String nor a byte[], is put only at an object
     * key: one whose name, the key's last part, has no suffix, or the suffix ".obj". At a key
     * with another suffix, such as "/notes/a.txt", the put throws IllegalArgumentException
     * ("Bad key"). The suffix is what follows the name's last '.' (the package's
     * {@linkplain bergdb.pub##objects Objects}).</p>
     *
     * <p>With key replace on, as the connection had it when w() made this builder, each
     * "${transactionTime}" in the key is replaced by the transaction's time
     * (Connection.setEnableKeyReplace(); bergdb 020-24-02, I-6).</p>
     *
     * @throws IllegalArgumentException
     *             If 'key' is null or otherwise invalid, or if object is null; or if it
     *             is a String with a lone surrogate, a char of U+D800 to U+DFFF that is not
     *             part of a surrogate pair, as a key with one is (bergdb 019-44), or whose
     *             UTF-8 takes more than 2^31 - 9 bytes, the most that a Java array holds
     *             (bergdb 020-08, section 3); or if it is an object with a string that has
     *             one, at any depth: the message names the field, and an array element's
     *             index (bergdb 021-04). Or if the object cannot be stored exactly (the
     *             package's {@linkplain bergdb.pub##objects Objects}; bergdb 020-09): its
     *             class, or a class it reaches, is not a Data Object class; an array in it
     *             has a null element; a value's class is not its field's type; it has a
     *             reference cycle, or is nested deeper than 16 levels of objects and arrays;
     *             or it is larger than a stored value may be. The message names the class
     *             or the place. A null field is not refused: it is left out, absent.
     * @throws IllegalStateException  If execute() was called: the builder is spent.
     */
    public WBuilder put(String key, Object object);
    
    /** 
     * Executes the puts and deletes as one transaction, and returns it when it has
     * committed. The builder is then spent, also if this method throws: a later put(),
     * delete() or execute() throws IllegalStateException.
     * 
     * @throws IllegalStateException  If execute() was called before: the builder is spent.
     * @throws bergdb.pub.util.DbException
     *             If the transaction is refused, nothing of it written, and the database
     *             goes on, as for Connection.put(): it is too large, about 1.88 GB in the
     *             stream, or the database is stopping or stopped. Or if the thread is
     *             interrupted while the transaction waits to run again after a conflict,
     *             which one with a put or a delete at an object key may meet, as it runs as
     *             an rw() does (bergdb 020-10, section 5.1): it is not run, and the thread's
     *             interrupt flag is set (Database, "Interrupts").
     * @throws bergdb.pub.util.DbFailedException
     *             If the database has failed, in this transaction or before: it then
     *             refuses every transaction and read until it is restarted. See
     *             Database.
     * @throws DataFormatException
     *             If one of its puts is of a byte[] that is an object of BergDB 2026.3 and
     *             before (format 1), at an object key of a directory with a user index,
     *             which no index can take (IndexBuilder, rule 1): nothing is written, and the
     *             database goes on.
     */
    public Transaction execute();
}
