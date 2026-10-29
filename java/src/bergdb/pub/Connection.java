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
 * @author Frans Lundberg
 */
public interface Connection extends ReadInterface {

    /**
     * If key replace is enabled, occurrences of the string "${transactionTime}"
     * in a database key will be replaced by the the unique transactionTime of
     * the transaction when it is executed. By default, the key replace feature
     * of a connection is disabled. This method must to be called to enable it.
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
     * operations are performed on the lastest database state.
     * Note that the requested lookup time is not always the same as the *actual*
     * lookup time used. If the requested lookup time is larger than the
     * transaction time of the last transaction, the transaction time of the
     * last transaction, is used as the actual lookup time.
     * </p>
     * 
     * <p>
     * A call to this method neutralize any effect from a previous call to
     * freezeLookupTime().
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
     * Returns the requested lookup time that was set with setLookupTime().
     */
    public Time getLookupTime();

    /**
     * After this method has been called, the actual lookup time of subsequent
     * read operations will be constant. The lookup time of this Connection will
     * not change until setLookupTime() is called or this method is called
     * again. This method is useful for reading a consistent state of the data
     * at one particular time using multiple read operations. The state stays readable
     * for the retain duration of the database (Database.setRetainDuration()); after that,
     * reads at the frozen time throw LookupTimeNotAvailableException.
     */
    public void freezeLookupTime();
    
    /**
     * <p>Returns the current based on the database clock. 
     * The returned time is guaranteed to be less then
     * the transaction time of any currently executing transaction (if any transaction is executing)
     * and less then the transaction time of any future transaction.
     * The returned time is also guaranteed to be greater than or equal to the transaction 
     * time of the last completed transaction.</p>
     */
    public Time currentTime();

    /**
     * Checks whether a key-value entry with the given key exists.
     * 
     * @param key
     *            The key to check for.
     * @return true if the key exists.
     * @throws IllegalArgumentException
     *             if 'key' is null.
     * @throws DbException
     *             Thrown if the database is faulty.
     * @throws DbFailedException
     *             If the database has failed, before or in this read (a read that fails
     *             on the storage fails it): it then refuses every transaction and read
     *             until it is restarted. See Database.
     */
    public boolean exists(String key);

    /**
     * Gets a single object stored in the database, or null if no entry exists
     * for the key. The caller specifies the class of the returned object. The
     * class must in general have a no-argement constructor which will be used
     * to create the object returned. The matching field of the object create
     * will be set based on the fields of the DbObject stored in the database.
     * 
     * @param key
     *            Database key of the object.
     * @param clazz
     *            Class of the object to create. The class must in general have
     *            a public no-argument constructor. Use DbObject.class to get
     *            the object data as it is stored in the database. Use
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
     * @return The object created based on 'clazz' and the data in the database,
     *             or null if there is no entry for the key.
     */
    public <TYPE> TYPE get(String key, Class<TYPE> clazz);
    
    /**
     * Returns information about the transaction that wrote the last
     * value retreived with the get() method: its time and its KVs. The KVs
     * are the user's; those that the database writes itself in the
     * transaction, the entries of an index, are left out.
     * This method call will always require a read from the database
     * storage, no caching for this query.
     *
     * @throws IllegalStateException
     *             If no get() has been made, or if the transaction that wrote the value
     *             was still being stored when get() read it (a get right after the put, in
     *             another thread): call get() again.
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
     *            The object to store. Cannot be null.
     * @throws DbException
     *             If the transaction could not be processed because the
     *             database is faulty.
     * @throws DbFailedException
     *             If the database has failed, in this transaction or before: it then
     *             refuses every transaction and read until it is restarted. See
     *             Database.
     * @throws IllegalArgumentException
     *             If 'key' is null or otherwise invalid, or if object is null.
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
     * @throws DbFailedException
     *             If the database has failed, in this transaction or before: it then
     *             refuses every transaction and read until it is restarted. See
     *             Database.
     */
    public Transaction rw(Action action);

    /**
     * Returns a builder use to create an iterator that can iterate objects
     * indexed by a secondary index called 'indexName'.
     * 
     * @param indexName
     *            The name of the index to use.
     * @param type
     *            The type of the objects to iterate.
     * @throws NoSuchIndexException
     *             if the index does not exist.
     */
    public <TYPE> UseIndexBuilder<TYPE> useIndex(String indexName, Class<TYPE> type)
            throws NoSuchIndexException;

    /**
     * Returns a builder used to create an iterator that can iterate objects
     * according to the primary key of the database.
     * 
     * @param type
     *            The type of the objects to iterate.
     * @throws NoSuchIndexException
     *             if the index does not exist.
     */
    public <TYPE> UsePrimaryBuilder<TYPE> usePrimary(Class<TYPE> type) throws NoSuchIndexException;

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