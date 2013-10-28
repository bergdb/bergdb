package bergdb.pub;

// TODO A. Consider methods: sync()/syncStrong().

/**
 * A connection to a Database is used to set and get data stored in the database.
 * Given a Connection, get operations [<code>c.get(..)</code>], 
 * set operations [<code>c.w().set(...execute()</code>], 
 * and rw-transactions [<code>c.rw(...).execute()</code>] can be executed.
 * A Connection object assumes it and any objects returned from its methods
 * are accessed from a single thread.
 * For multi-threaded access to the database, create a Connection object for each thread.
 * 
 * @author Frans Lundberg
 */
public interface Connection extends ReadInterface {
    
    /**
     * <p>Sets the requested lookup time to use for subsequent calls to: get(), exists().
     * By default, the requested lookup time is Long.MAX_VALUE. This means that read operations
     * are performed on the last database state.
     * Note that the requested lookup time is not always the same as the *actual* lookup time used.
     * If the requested lookup time is larger than the transaction time of the last transaction,
     * the transaction time of the last transaction, is used as the actual lookup time.</p>
     * 
     * <p>A call to this method neutralize any effect from a previous call to freezeLookupTime().</p>
     * 
     * @param lookupTime The database time to use for read operations. Use Long.MAX_VALUE
     * to read the last database state.
     * @throws IllegalArgumentException If lookupTime is negative.
     */
    public void setLookupTime(long lookupTime);
    
    /**
     * Returns the actual lookup time that was used for the last read operation.
     */
    public long getActualLookupTime();
    
    /**
     * After this method has been called, the actual lookup time of subsequent read operations will
     * be constant. The lookup time of this Connection will not change until setLookupTime() is 
     * called or this method is called again. This method is useful for reading a consistent 
     * state of the data at one particular time using multiple read operations.
     */
    public void freezeLookupTime();
    
    /**
     * If key replace is enabled, occurrences of the string "${transactionTime}" in a database
     * key will be replaced by the the unique transactionTime of the transaction when it 
     * is executed. By default, the key replace feature of a connection is disabled.
     * This method must to be called to enable it.
     * The transactionTime of the transaction functions as a unique transaction ID. 
     * It is guaranteed to be unique for every transaction and is strictly increasing.
     * 
     * @param enable  Set to true to enable key replace.
     */
    public void setEnableKeyReplace(boolean enable);
    
    /**
     * Returns true if key replace is enabled and false otherwise.
     */
    public boolean getEnableKeyReplace();
    
    /**
     * Checks whether a key-value pair with the given key exists.
     * 
     * @param key
     *            The key to check.
     * @return True if the key exists.
     * @throws IllegalArgumentException
     *             if 'key' is null.
     * @throws DbException
     *             Thrown if the database is faulty.
     */
    public boolean exists(String key);
    
    /**
     * Gets a single object stored in the database.
     * 
     * @param key
     *              Database key of the object.
     * @param clazz
     *              Class of the object to create. The class must in general have
     *              a public non-argument constructor.
     * @throws NoSuchObjectException
     *              Thrown if there is no object in the database for the given key.
     * @throws NoFieldsSetException
     *              If no fields of object to be returned were set.
     *              Not applicable when clazz is String.class or byte[].class.
     * @throws DbException
     *              Thrown if the database is faulty.
     * @throws IllegalArgumentException
     *              If key does not follow the allowed format, or is null. 
     *              If 'clazz' is null.
     * @return The object created based on 'clazz' and the data in the database.
     */
    public <TYPE> TYPE get(String key, Class<TYPE> clazz);
    
    /**
     * Stores a single object to the database.
     * The transaction is executed immediately without an explicit call to execute().
     * 
     * @param key
     * @param object
     */
    // TODO A. Document. Exceptions...
    public Transaction put(String key, Object object);
    
    /**
     * Stores a single object using the 'key' field as the database key.
     * The transaction is executed immediately without an explicit call to execute().
     * 
     * @param object
     */
    // TODO A. Document. Exceptions...
    public Transaction put(Object object);
    
    /**
     * Creates a builder object used to build a write transaction.
     */
    public WBuilder w();
    
    /**
     * Creates an RW transaction given its transaction action.
     */
    public Transaction rw(Action action);
    
    /**
     * Returns a builder use to create an iterator that can iterate objects indexed
     * by a secondary index called 'indexName'.
     * 
     * @param indexName  The name of the index to use.
     * @param type  The type of the objects to iterate. In C#, use the typeof() operator.
     * @throws NoSuchIndexException if the index does not exist.
     */
    public <TYPE> UseIndexBuilder<TYPE> useIndex(String indexName, Class<TYPE> type) 
            throws NoSuchIndexException;
    
    /**
     * Returns a builder used to create an iterator that can iterate objects according to 
     * the primary key of the database.
     * 
     * @param type  The type of the objects to iterate. In C#, use the typeof() operator.
     * @throws NoSuchIndexException if the index does not exist.
     */
    public <TYPE> UsePrimaryBuilder<TYPE> usePrimary(Class<TYPE> type) 
            throws NoSuchIndexException;
}

/*

Log
===

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
two method calls.

java.util.Map.get(key) returns null if the map contains no mapping for the key.

== Index iterators ==

Should index() return empty iterators, or throw an exception if index does not exist for the 
lookup time? In a way, it makes sense to return an empty iterator. On the other hand, for most 
cases, the caller expects an existing index and throwing an explicit exception would be best
to report the error conditions are early as possible.

Conclusion 2012-10: Use exceptions!

== Lookup time ==

A connection can store state. We could store lookupTime in the connection.
setLookupTime(). It would reduce the API "surface". Default would be Long.MAX_VALUE, of course.
We should also have a setLookupTime(String timeString). 

== String time ==

A UTC time string, or local time even. Can also be relative to current time. 
Examples: "today" (00:00:00 today), "-10 sec" (ten seconds ago). The time string is 
resolved to an absolute time given the time zone of the connection (of database?) and the 
current database time.

*/