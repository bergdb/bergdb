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
 * <p><b>A refused put() or delete() spoils the builder</b> (bergdb 024-26, U26-5): the
 * transaction writes all of its puts and deletes, or none. A put() or delete() that throws,
 * as one refused with IllegalArgumentException for its key or value (a key over 111 bytes, a
 * value over 8 MiB; the package's {@linkplain bergdb.pub##limits Limits}), adds nothing to
 * the transaction and spoils the builder: execute() then throws IllegalStateException and
 * writes nothing, also when the caller caught the refusal, and so does every later put() and
 * delete(), at once. The message names the first refused call, and its exception is the
 * cause. For the other writes, get a new builder and put them again. Until release 2026.5 a
 * caller that caught the refusal and called execute() committed the other puts. A key made
 * by the program is checked before the call with {@link Limits#checkKey(String)} or
 * {@link Limits#keyBytes(String)} (bergdb 026-02).</p>
 *
 * <p>execute() spends the builder, also when it throws, except when it throws because
 * another thread is in a call of the connection (below), which leaves the builder unspent:
 * a later put(), delete() or execute() throws IllegalStateException (bergdb 020-21, 2;
 * 021-22). For another transaction, get a new builder.</p>
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
     * @throws IllegalArgumentException  If 'key' is null or otherwise invalid, or has more
     *             than 111 bytes as stored (L2). The delete is not added, and the builder is
     *             spoiled: execute() writes nothing (the class Javadoc).
     * @throws IllegalStateException  If execute() was called: the builder is spent. Or if
     *             the builder is spoiled: an earlier put() or delete() was refused.
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
     *             If 'key' is null or otherwise invalid, or has more than 111 bytes as
     *             stored, its UTF-8 and a byte for each part (L2), or if object is null; or
     *             if it is a String with a lone surrogate, a char of U+D800 to U+DFFF that
     *             is not part of a surrogate pair, as a key with one is (bergdb 019-44), or
     *             a value of more than 8 MiB, a byte[] or a String's UTF-8 (L4; the
     *             package's {@linkplain bergdb.pub##limits Limits}; bergdb 024-17); or if
     *             it is an object with a string that has
     *             one, at any depth: the message names the field, and an array element's
     *             index (bergdb 021-04). Or if the object cannot be stored exactly (the
     *             package's {@linkplain bergdb.pub##objects Objects}; bergdb 020-09): its
     *             class, or a class it reaches, is not a Data Object class; an array in it
     *             has a null element; a value's class is not its field's type; it has a
     *             reference cycle, or is nested deeper than 16 levels of objects and arrays;
     *             or its stored value is larger than 8 MiB (L4), counted before anything is
     *             copied (bergdb 021-23; 024-17). The message names the
     *             class or the place. A null field is not refused: it is left out, absent.
     *             The put is not added, and the builder is spoiled: execute() writes
     *             nothing (the class Javadoc).
     * @throws IllegalStateException  If execute() was called: the builder is spent. Or if
     *             the builder is spoiled: an earlier put() or delete() was refused.
     */
    public WBuilder put(String key, Object object);
    
    /** 
     * Executes the puts and deletes as one transaction, and returns it when it has
     * committed. The builder is then spent, also if this method throws, except for the
     * IllegalStateException of a connection that another thread is in a call of: a later
     * put(), delete() or execute() throws IllegalStateException.
     * 
     * @throws IllegalStateException  If execute() was called before: the builder is spent.
     *             Or if another thread is in a call of the connection (Connection,
     *             "Threads"; bergdb 021-22): nothing is run, and the builder is left
     *             unspent. Or if the builder is spoiled: a put() or delete() of it was
     *             refused, and nothing is written, none of its other puts and deletes
     *             either (the class Javadoc); the message names the first refused call.
     * @throws bergdb.pub.util.DbException
     *             If the transaction is refused, nothing of it written, and the database
     *             goes on, as for Connection.put(): it passes a limit of a transaction,
     *             500 operations, 56 KiB of keys or 32 MiB of keys and values (the package's
     *             {@linkplain bergdb.pub##limits Limits}; bergdb 024-17), or the database is
     *             stopping or
     *             stopped. Or if key replace makes two of its keys one key, such as a put at
     *             "/t/${transactionTime}.txt" and one at the key with the transaction's time
     *             written out (Connection.setEnableKeyReplace(); bergdb 024-16): it is not
     *             run again. Or if the thread is interrupted while the transaction waits to
     *             run again after a conflict, which one with a put or a delete at an object
     *             key may meet, as it runs as an rw() does (bergdb 020-10, section 5.1): it
     *             is not run, and the thread's interrupt flag is set (Database,
     *             "Interrupts").
     * @throws bergdb.pub.util.DbFailedException
     *             If the database has failed, in this transaction or before: it then
     *             refuses every transaction and read until it is restarted. See
     *             Database.
     * @throws DataFormatException
     *             If one of its puts is of a byte[] that is an object of BergDB 2026.3 and
     *             before (format 1), at an object key of a directory with a user index,
     *             which no index can take (IndexBuilder, rule 1): nothing is written, and the
     *             database goes on.
     * @throws IllegalArgumentException
     *             If one of its puts is of an object whose levels for an index of its
     *             directory take more than 111 bytes (L6; the package's
     *             {@linkplain bergdb.pub##limits Limits}; bergdb 024-17, QL4): nothing is
     *             written, and the database goes on.
     */
    public Transaction execute();
}
