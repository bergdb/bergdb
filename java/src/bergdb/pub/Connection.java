package bergdb.pub;

import bergdb.pub.util.DbException;
import bergdb.pub.util.DbFailedException;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.pub.util.SyncLevel;

/**
 * A connection to a Database is used to put and get data stored in the
 * database. Given a Connection, get operations [<code>c.get(..)</code>], put
 * operations [<code>c.w().put(...execute()</code> or <code>c.put(...)</code>],
 * and rw-transactions [<code>c.rw(...)</code>] can be executed. A
 * Connection object assumes it and any objects returned from its methods are
 * accessed from a single thread. For multi-threaded access to the database,
 * create a Connection object for each thread by calling Database.newConnection().
 * 
 * <p>Keys. A key starts with '/', has at least one more character, does not end with '/',
 * and has no "//" and no lone surrogate (bergdb 015-49); every call that takes a key refuses
 * another key, and null, with IllegalArgumentException.</p>
 *
 * <p>Strings. Every string BergDB stores, a key, a String value and each string in an
 * object, is Unicode text stored as well-formed UTF-8; a put refuses a String with a lone
 * surrogate with IllegalArgumentException. The rule in full: the package's
 * {@linkplain bergdb.pub##strings Strings} (bergdb 021-04).</p>
 *
 * <p>Objects. A value that is neither a String nor a byte[] is an object of a Data Object
 * class: public, with a public no-argument constructor and public fields. A put stores it
 * exactly and leaves a null field out; a get converts each stored field to its field's type,
 * best effort, and leaves an absent field as the class's constructor set it. The rules: the
 * package's {@linkplain bergdb.pub##objects Objects} and
 * {@linkplain bergdb.pub##null Null and absent fields} (bergdb 020-09).</p>
 *
 * <p>After a DbFailedException, or an Error such as an OutOfMemoryError, the application
 * should end its process: the database, or its environment, has failed (Database,
 * "Errors"; bergdb 019-10).</p>
 * 
 * @author Frans Lundberg
 */
public interface Connection extends ReadInterface {

    /**
     * If key replace is enabled, occurrences of the string "${transactionTime}"
     * in the key of a put will be replaced by the unique transactionTime of
     * the transaction when it is executed. A delete's key is taken as written
     * (bergdb 019-15). In an object key (no suffix, or ".obj"), "${transactionTime}" may
     * be in the name only, the part after the last '/': a put with it in the directory
     * throws IllegalArgumentException, as the indexes of the directory that the put lands
     * in would not be known before the transaction's time (bergdb 020-14, X1). A key with
     * another suffix is never indexed, and is replaced anywhere. By default, the key
     * replace feature of a connection is disabled. This method must be called to enable it.
     * The transaction time of the transaction functions as a unique transaction ID.
     * It is guaranteed to be unique for every transaction and is strictly increasing.
     * 
     * @param enable
     *            Set to true to enable key replace.
     */
    public void setEnableKeyReplace(boolean enable);

    /**
     * Returns true if key replace is enabled and false otherwise.
     */
    public boolean getEnableKeyReplace();

    /**
     * <p>
     * Sets the requested lookup time to use for subsequent calls to: get(),
     * exists(), useIndex(), usePrimary().
     * By default, the requested lookup time is Time.MAX. This means that read 
     * operations are performed on the latest database state.
     * Note that the requested lookup time is not always the same as the *actual*
     * lookup time used. If the requested lookup time is larger than the
     * transaction time of the last transaction, the transaction time of the
     * last transaction, is used as the actual lookup time.
     * </p>
     * 
     * <p>
     * A call to this method undoes the effect of a previous call to freezeLookupTime(),
     * and a later call to freezeLookupTime() undoes this one's (bergdb 018-04, Q2).
     * </p>
     * 
     * <p>
     * A lookup time before Database.getFirstAvailableLookupTime() cannot be read: the read
     * throws LookupTimeNotAvailableException. This can happen to a read that has already
     * started, and to later reads with the same lookup time, when the database reclaims
     * old data (see Database.setRetainDuration()). A reader that needs a state older than
     * the retain duration must not rely on it staying available; it can catch the exception
     * and retry with a later time.
     * </p>
     *
     * @param lookupTime
     *            The database time to use for read operations. Use
     *            Time.MAX to read the latest database state.
     */
    public void setLookupTime(Time lookupTime);
    
    /**
     * Returns the lookup time of this connection: Time.MAX by default, and t after
     * setLookupTime(t). After freezeLookupTime(), it is Time.MAX until the next read, and
     * the frozen time after it: with setLookupTime(), another connection can then read the
     * same state (bergdb 018-04, Q3).
     */
    public Time getLookupTime();

    /**
     * Freezes the lookup time at the latest state as of the next read. It sets the lookup
     * time to Time.MAX; the next read of this connection, a get(), an exists(), a useIndex()
     * or a usePrimary(), sets it to the time it read at, and later reads read at that time,
     * until setLookupTime() or this method is called again (bergdb 020-10, section 3.6). Each call freezes anew, at the latest state as of the next read,
     * also after setLookupTime(t): it does not freeze t (bergdb 018-04, Q2).
     * This method is useful for reading a consistent state of the data
     * at one particular time using multiple read operations. The state stays readable
     * for the retain duration of the database (Database.setRetainDuration()); after that,
     * reads at the frozen time throw LookupTimeNotAvailableException.
     */
    public void freezeLookupTime();
    
    /**
     * <p>Returns the current time of the database clock.
     * The returned time is guaranteed to be less than
     * the transaction time of any currently executing transaction (if any transaction is executing)
     * and less than the transaction time of any future transaction.
     * The returned time is also guaranteed to be greater than or equal to the transaction 
     * time of the last completed transaction.</p>
     *
     * <p>These promises are for this started database: after a restart, with a clock
     * that has not moved (a test clock), the first transaction can have the time that
     * currentTime() returned before the restart (bergdb 018-04, Q5).</p>
     */
    public Time currentTime();

    /**
     * Checks whether a key-value entry with the given key exists.
     *
     * <p>A read like get(): it reads at the connection's lookup time, and after
     * freezeLookupTime(), as the first read, it freezes the time it read at (bergdb
     * 015-48). When it finds the key, transactionInfo() then describes the transaction
     * that wrote the value, as after a get() that retrieved it; when it does not, it
     * leaves transactionInfo() as a get() that finds no entry does.</p>
     * 
     * @param key
     *            The key to check for.
     * @return true if the key exists.
     * @throws IllegalArgumentException
     *             If key does not follow the allowed format, or is null, as for get()
     *             and an rw-transaction's exists() (bergdb 019-05).
     * @throws DbException
     *             Thrown if the database is faulty.
     * @throws DbFailedException
     *             If the database has failed, before or in this read (a read that fails
     *             on the storage fails it): it then refuses every transaction and read
     *             until it is restarted. See Database.
     */
    public boolean exists(String key);

    /**
     * Gets the value at the key, or null if no entry exists for the key, as an object
     * of the class the caller gives: a String (the value's UTF-8 bytes decoded) or a
     * byte[]. For another class, a Data Object class (the package's
     * {@linkplain bergdb.pub##objects Objects}), a new object of it is made by its public
     * no-argument constructor, and each of its stored fields that the stored object has is
     * set from it, converted to the field's type best effort; a field that the stored
     * object does not have keeps the constructor's value (bergdb 020-09).
     *
     * <p>A byte[] returned (by byte[].class, or by Object.class at a value of bytes) is
     * the database's own array, not a copy: do not change it. A change of it changes
     * what later reads return, in every connection, until the value leaves memory or
     * the database restarts, while the stream keeps the committed bytes. To change
     * the bytes, copy them first, with clone() (bergdb 015-47).</p>
     *
     * <p>Object.class gives a DbObject for a stored object: a value at an object key (no
     * suffix, or ".obj") that starts with the object format's header, 0x82, and passes the
     * format's full check; a String at a key with the suffix ".txt"; else the value's bytes.
     * A value has no type of its own, so this is a guess: a byte[] put whose bytes are a
     * stored object is read as one. An object of BergDB 2026.3 and before (format 1) is told
     * by its structure, "bergo", the version 1, a field count and a field table that fits
     * the value, and refused: a value that only starts with "bergo" and the version 1, as a
     * String may, is not one, but a String or a byte[] whose bytes happen to be a whole
     * object of format 1, such as "bergo" and the chars U+0001, U+0000 and U+0000, is
     * (bergdb 020-08, section 3).</p>
     * 
     * @param key
     *            Database key of the object.
     * @param clazz
     *            Class of the object to create: a Data Object class, or a primitive, its
     *            wrapper or an array class for a value put as one. Use DbObject.class to
     *            get the object data as it is stored in the database. Use
     *            byte[].class to get the raw bytes as stored in the database.
     *            Use String.class to read a String directly from the raw value
     *            bytes assuming that the value stored consists of UTF-8 bytes.
     * @throws DbException
     *             Thrown if the database is faulty.
     * @throws DbFailedException
     *             If the database has failed, before or in this read (a read that fails
     *             on the storage fails it): it then refuses every transaction and read
     *             until it is restarted. See Database.
     * @throws IllegalArgumentException
     *             If key does not follow the allowed format, or is null. If
     *             'clazz' is null.
     * @throws DataFormatException
     *             If clazz is String.class, or Object.class at a key with the suffix
     *             ".txt", and the value is not well-formed UTF-8: every string in BergDB
     *             is, and a reader never repairs one that is not, written through the Core
     *             API or by another writer (bergdb 021-06). Read it as a byte[].
     * @throws ObjectCreationException
     *             If clazz is not a Data Object class, or reaches one that is not through
     *             its fields' types, checked also when the key has no value; if a
     *             constructor throws (its exception the cause); if the value is not a stored
     *             object, such as one of BergDB 2026.3 and before (format 1, also as
     *             Object.class, see above). Never for a stored value that does not fit its
     *             field: it is converted (bergdb 020-09, section 5.2).
     * @return The object created based on 'clazz' and the data in the database,
     *             or null if there is no entry for the key.
     */
    public <TYPE> TYPE get(String key, Class<TYPE> clazz);
    
    /**
     * Returns information about the transaction that wrote the last
     * value retrieved with the get() method: its time and its KVs. The KVs
     * are the user's; those that the database writes itself in the
     * transaction, the entries of an index, are left out.
     * A get() that finds no entry does not change the value this method describes:
     * after one, it describes the value retrieved by an earlier get().
     * An exists() of this connection counts as a get() here: one that finds the key as
     * a get() that retrieved its value, one that does not as a get() that found no entry.
     * This method call will always require a read from the database
     * storage, no caching for this query.
     *
     * @throws IllegalStateException
     *             If no get() has retrieved a value: none has been made, or each found no
     *             entry. Or if the transaction that wrote the value was still being stored
     *             when get() read it (a get right after the put, in another thread): call
     *             get() again.
     * @throws DbFailedException
     *             If the database has failed, before or in this read: it then refuses
     *             every transaction and read until it is restarted. See Database.
     * @throws LookupTimeNotAvailableException
     *             If the database has reclaimed the transaction: the lookup time of the
     *             get is no longer available, or reclaim has rewritten the value, in a
     *             transaction of its own, so that the transaction that wrote it can be cut.
     */
    public TransactionInfo transactionInfo();

    /**
     * Puts a key-value entry to the database. If an entry with the given key
     * already exists, it is overwritten. The transaction is executed
     * immediately in this method.
     *
     * @param key
     *            The key of the key-value entry. Must begin with "/".
     * @param object
     *            The object to store. Cannot be null. A byte[] is copied at
     *            the put: the caller may change or reuse its array afterwards.
     *            A String, and each string in an object, is stored as well-formed
     *            UTF-8 (the package's {@linkplain bergdb.pub##strings Strings}).
     *            An object, neither a String nor a byte[], is put only at an object
     *            key, one without a suffix or with ".obj"; at another key the put
     *            throws IllegalArgumentException, as for WBuilder.put() (the package's
     *            {@linkplain bergdb.pub##objects Objects}).
     * @throws DbException
     *             If the transaction could not be processed because the
     *             database is faulty.
     * @throws DbFailedException
     *             If the database has failed, in this transaction or before: it then
     *             refuses every transaction and read until it is restarted. See
     *             Database.
     * @throws IllegalArgumentException
     *             If 'key' is null or otherwise invalid, or if object is null; or if it
     *             is a String with a lone surrogate, or an object with a string that has
     *             one, as for WBuilder.put() (the package's
     *             {@linkplain bergdb.pub##strings Strings}; bergdb 019-44, 021-04); or if
     *             the object cannot be stored exactly, as for WBuilder.put().
     * @throws DataFormatException
     *             If it puts a byte[] that is an object of BergDB 2026.3 and before (format
     *             1) at an object key of a directory with a user index, which no index can
     *             take (IndexBuilder, rule 1): nothing is written, and the database goes on.
     */
    public Transaction put(String key, Object object);

    /**
     * Deletes a key-value entry from the database. If an entry with the given key
     * does not exists this method does nothing.
     * 
     * @param key
     *             The key of the key-value entry. Must begin with "/".
     * @throws DbException
     *             If the transaction could not be processed because the
     *             database is faulty.
     * @throws DbFailedException
     *             If the database has failed, in this transaction or before: it then
     *             refuses every transaction and read until it is restarted. See
     *             Database.
     * @throws IllegalArgumentException
     *             If 'key' is null or otherwise invalid.
     */
    public Transaction delete(String key);   

    /**
     * Creates a builder object used to build a write-only transaction.
     */
    public WBuilder w();

    /**
     * Executes an RW transaction given its action, and returns it once it has committed.
     * The action may run more than once (Action.run()). Its results for the caller go
     * through outputs: RwEnvironment.setOutput() in the action, Transaction.getOutput()
     * on the returned transaction.
     * 
     * <p>A transaction that conflicts with another is rerun after a short sleep (10 ms,
     * doubling up to 640 ms) until it commits. Under overload it may never commit: for
     * example, a long action while other transactions write more than about 100,000 keys,
     * since the conflict history covers only the last 96,000 to 128,000 written keys and
     * every attempt is then refused (bergdb 015-88).</p>
     * 
     * @throws DbFailedException
     *             If the database has failed, in this transaction or before: it then
     *             refuses every transaction and read until it is restarted. See
     *             Database.
     * @throws DataFormatException
     *             If the action puts a byte[] that is an object of BergDB 2026.3 and before (format
     *             1) at an object key of a directory with a user index, which no index can
     *             take (IndexBuilder, rule 1): nothing is written, and the database goes on.
     */
    public Transaction rw(Action action);

    /**
     * A scan of the user index of the name (see UseIndexBuilder; bergdb 020-10, sections 3.4
     * and 3.6). The index's definition is read at the connection's lookup time, resolved to
     * an actual time t at this call; the index must exist and be active at t. Every iterator
     * of the builder reads the index's entries and values at t, also when the index was
     * deleted since t, until the first available lookup time passes t: then an iterator
     * throws LookupTimeNotAvailableException from hasNext() or next().
     *
     * <p>A read for freezeLookupTime(): the first read after it, whether a get(), an
     * exists(), a useIndex() or a usePrimary(), fixes the frozen time. A scan does not change
     * transactionInfo(), which describes get() and exists() only.</p>
     * 
     * @param indexName
     *            The name of the index to use.
     * @param type
     *            The type of the objects to iterate, as for get(String, Class). With
     *            byte[].class or Object.class, an array returned is the database's own, as
     *            with get(String, Class): do not change it.
     * @throws NoSuchIndexException
     *             If there is no index of the name at t, or it is building at t.
     * @throws ObjectCreationException
     *             If 'type' is not a class that a get takes (bergdb 020-09, section 3.3),
     *             whatever the data.
     * @throws IllegalArgumentException
     *             If 'indexName' or 'type' is null.
     */
    public <TYPE> UseIndexBuilder<TYPE> useIndex(String indexName, Class<TYPE> type)
            throws NoSuchIndexException;

    /**
     * A listing of one directory's keys in key order, with their values converted to 'type'
     * (see UsePrimaryBuilder; bergdb 020-10, sections 3.5 and 3.6). Its lookup time is the
     * connection's, resolved to an actual time at this call; every iterator of the builder
     * reads at that time.
     *
     * <p>A read for freezeLookupTime(), as useIndex() is; it does not change
     * transactionInfo().</p>
     * 
     * @param type
     *            The type of the values listed, as for get(String, Class). With byte[].class
     *            or Object.class, an array returned is the database's own, as with
     *            get(String, Class): do not change it.
     * @throws ObjectCreationException
     *             If 'type' is not a class that a get takes (bergdb 020-09, section 3.3),
     *             whatever the data.
     * @throws IllegalArgumentException
     *             If 'type' is null.
     */
    public <TYPE> UsePrimaryBuilder<TYPE> usePrimary(Class<TYPE> type);

    /**
     * Waits until ordinary durability has been achieved for the last
     * transaction started with this connection.
     * 
     * @throws DbException if the database is faulty, or if the thread is interrupted while
     *             it waits: the transaction stays committed (see Database.sync()).
     * @throws DbFailedException
     *             If the storage has failed: the database fails. See Database.
     */
    public void sync();

    /**
     * Waits until the specified sync level (durability) has been achieved 
     * for the last transaction started with this connection.
     *
     * @throws DbFailedException
     *             If the storage has failed: the database fails. See Database.
     */
    public void sync(SyncLevel syncLevel);
}

/*

Log
===

140721 syncString deprecated since 2014.1.
140720 rw() now executes transaction immediately.
140715 Added setLookupTime() now takes a Time.
131028 Added sync()/syncStrong().
1310xx Changed "set" to "put".
130605 Added usePrimary() method that returns a PrimaryIterBuilder and some renaming.
130602 Added primary() method.
130310 Changed to a single get method: public <TYPE> TYPE get(String key, Class<TYPE> clazz);
121029 Fixed index(), dir() methods to have type-safe implementations.
121004 Added setLookupTime instead of using parameter for each read operation.


Discussion
==========

== Null vs exception ==

Return null from get() if no such object exists or throw exception?
This depends. See http://stackoverflow.com/questions/175532/should-a-retrieval-method-return-null-or-throw-an-exception-when-it-cant-prod
I like exceptions in general. But in some cases, the condition that there is
no such object is normal, not exceptional. Can be tested with exists(), but that requires
two method calls. java.util.Map.get(key) returns null if the map contains no mapping for the key.

== Index iterators ==

Should index() return empty iterators, or throw an exception if index does not exist for the 
lookup time? In a way, it makes sense to return an empty iterator. On the other hand, for most 
cases, the caller expects an existing index and throwing an explicit exception would be best
to report the error condition as early as possible. Conclusion 2012-10: Use exceptions!

*/