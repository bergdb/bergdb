package bergdb.pub;

/**
 * A connection to a Database is used to put and get data stored in the
 * database. Given a Connection, get operations [<code>c.get(..)</code>], put
 * operations [<code>c.w().set(...execute()</code> or <code>c.put(...)</code>],
 * and rw-transactions [<code>c.rw(...).execute()</code>] can be executed. A
 * Connection object assumes it and any objects returned from its methods are
 * accessed from a single thread. For multi-threaded access to the database,
 * create a Connection object for each thread.
 * 
 * @author Frans Lundberg
 */
public interface Connection extends ReadInterface {

    /**
     * <p>
     * Sets the requested lookup time to use for subsequent calls to: get(),
     * exists(). By default, the requested lookup time is Long.MAX_VALUE. This
     * means that read operations are performed on the last database state. Note
     * that the requested lookup time is not always the same as the *actual*
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
     * @param lookupTime
     *            The database time to use for read operations. Use
     *            Long.MAX_VALUE to read the last database state.
     * @throws IllegalArgumentException
     *             If lookupTime is negative.
     */
    public void setLookupTime(long lookupTime);

    /**
     * Returns the actual lookup time that was used for the last read operation.
     */
    public long getActualLookupTime();

    /**
     * After this method has been called, the actual lookup time of subsequent
     * read operations will be constant. The lookup time of this Connection will
     * not change until setLookupTime() is called or this method is called
     * again. This method is useful for reading a consistent state of the data
     * at one particular time using multiple read operations.
     */
    public void freezeLookupTime();

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
     * Checks whether a key-value entry with the given key exists.
     * 
     * @param key
     *            The key to check for.
     * @return true if the key exists.
     * @throws IllegalArgumentException
     *             if 'key' is null.
     * @throws DbException
     *             Thrown if the database is faulty.
     */
    public boolean exists(String key);

    /**
     * Gets a single object stored in the database. If no entry exists for the
     * key, a NoSuchObjectException is thrown. The caller specifies the class of
     * the returned object. The class must in general have a no-argement
     * constructor which will be used to create the object returned. The
     * matching field of the object create will be set based on the fields of
     * the DbObject stored in the database. If no fields are set, an exception
     * is thrown.
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
     * @throws NoSuchObjectException
     *             Thrown if there is no object in the database for the given
     *             key.
     * @throws NoFieldsSetException
     *             If no fields of object to be returned were set. Not
     *             applicable when clazz is String.class or byte[].class.
     * @throws DbException
     *             Thrown if the database is faulty.
     * @throws IllegalArgumentException
     *             If key does not follow the allowed format, or is null. If
     *             'clazz' is null.
     * @return The object created based on 'clazz' and the data in the database.
     */
    public <TYPE> TYPE get(String key, Class<TYPE> clazz);

    /**
     * Puts a key-object entry to the database. If an entry with the given key
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
     * @throws IllegalArgumentException
     *             If 'key' is null or otherwise invalid, or if object is null.
     */
    public Transaction put(String key, Object object);

    /**
     * Stores a single object to the database using the 'key' field of the
     * object as the key. The object must have a field of type String and name
     * 'key', otherwise an exception is thrown. If an entry with the given key
     * already exists, it is overwritten. The transaction is executed
     * immediately in this method.
     * 
     * @param object
     *            The object to store. Cannot be null and must have a String
     *            field named 'key'.
     * @throws DbException
     *             If the transaction could not be processed because the
     *             database is faulty.
     * @throws MissingKeyFieldException
     *             If 'object' does not have a String field named 'key'.
     * @throws IllegalArgumentException
     *             If the key field string is null or otherwise invalid, or if
     *             object is null.
     */
    public Transaction put(Object object);

    /**
     * Creates a builder object used to build a write-only transaction.
     */
    public WBuilder w();

    /**
     * Creates an RW transaction given its action.
     */
    public Transaction rw(Action action);

    /**
     * Returns a builder use to create an iterator that can iterate objects
     * indexed by a secondary index called 'indexName'.
     * 
     * @param indexName
     *            The name of the index to use.
     * @param type
     *            The type of the objects to iterate. In C#, use the typeof()
     *            operator.
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
     *            The type of the objects to iterate. In C#, use the typeof()
     *            operator.
     * @throws NoSuchIndexException
     *             if the index does not exist.
     */
    public <TYPE> UsePrimaryBuilder<TYPE> usePrimary(Class<TYPE> type) throws NoSuchIndexException;

    /**
     * Waits until ordinary durability has been achieved for the last
     * transaction started with this connection.
     * 
     * @throws DbException if the database is faulty.
     */
    public void sync();

    /**
     * Waits until strong durability has been achieved for the last transaction
     * started with this connection.
     * 
     * @throws DbException is the database is faulty.
     */
    public void syncStrong();
}

/*

Log
===

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
Conclusion: Use exception.

== Index iterators ==

Should index() return empty iterators, or throw an exception if index does not exist for the 
lookup time? In a way, it makes sense to return an empty iterator. On the other hand, for most 
cases, the caller expects an existing index and throwing an explicit exception would be best
to report the error conditions are early as possible. 
Conclusion 2012-10: Use exceptions!

*/