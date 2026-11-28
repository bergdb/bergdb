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
 * connection is used by one thread at a time (Threads, below).
 *
 * <p>Threads (bergdb 021-22). A connection is used by one thread at a time: a call of it
 * while another thread is in a call of the same connection throws IllegalStateException,
 * and reads and changes nothing. That holds for every call that reads, writes, runs a
 * transaction (also execute() of a WBuilder from w()), syncs, starts a scan, or sets the
 * lookup time or key replace; Database.connection() too, in the thread whose connection
 * it is, as it sets its lookup time. A call inside a call of the same thread is taken, such
 * as a get in a Data Object constructor that a get runs, or a put in an rw() action. An
 * iterator of usePrimary() or useIndex() is for one thread at a time in the same way:
 * hasNext() or next() while another thread is in one of them throws IllegalStateException.
 * A WBuilder that threads share takes their calls one at a time (WBuilder). An rw() action
 * may use its environment from several threads (RwEnvironment).</p>
 *
 * <p>Each thread uses a connection of its own: Database.connection() gives the calling
 * thread its connection, the same object at each call in that thread, and is the one to use.
 * Database.newConnection() makes another, for a second view in a thread, such as a reader at
 * another lookup time, which the thread keeps (bergdb 020-24-03, U3-8). connection() sets the
 * lookup time of the thread's connection to Time.MAX at each call, also while a caller
 * reads a frozen or an earlier state through it; code that reads at a lookup time keeps the
 * connection it set it on, or uses one from newConnection().</p>
 * 
 * <p>Keys. A key starts with '/', has at least one more character, does not end with '/',
 * and has no "//" and no lone surrogate (bergdb 015-49); every call that takes a key refuses
 * another key, and null, with IllegalArgumentException. A put or a delete refuses a key of
 * more than 111 bytes as stored, its UTF-8 and one byte more for each '/' (the package's
 * {@linkplain bergdb.pub##limits Limits}; bergdb 024-17, L2); {@link Limits#keyBytes(String)}
 * counts them and {@link Limits#checkKey(String)} checks a key before a call. A key is
 * stored as a path of key nodes, a level for each 7 bytes of the key, so that a key costs
 * stream bytes, memory and time in proportion to its length, many times what a value of
 * that length costs. In a test
 * of 200,000 keys, each with a String value of 11 bytes, written 1,000 to a transaction, a
 * key of 13 bytes took about 70 bytes of the stream, and a key of 114 bytes whose first 100
 * differ from key to key about 1,200 to 1,400 bytes; keys of 120 bytes that shared their
 * first 109 took about 190 (bergdb 020-24-13, U13-1). Keys share key nodes by their starts
 * of 7, 14, 21 bytes, a key's bytes being its UTF-8 and one more for each '/'. A start of
 * 7, 14 or 21 bytes that no other key has, the whole key included when it has exactly 7,
 * 14 or 21 bytes, costs a key node of its own, about 226 bytes of heap while in memory; so
 * one byte more or less of a key or of a common prefix can add or save a key node a key.
 * With empty values and every node in memory, a million keys that shared their starts took
 * about 130 bytes of heap a key (127 at ten million), keys of 7 bytes 356, and random keys,
 * put in random order, of 6 bytes 181 and of 36 bytes, such as UUIDs, 1,305 (bergdb
 * 024-08, sections 5 and 7).
 * With a cache budget below the data (DatabaseBuilder.cacheSizeInMb()) the heap stays near
 * the budget whatever the keys, and the nodes cost stream bytes and time instead: 3 million
 * keys of 32 random hex digits, put in random order, wrote 819 bytes of the stream a put
 * and read 5.6 nodes from the stream a get, and a put took 4.6 times as long, against 226
 * bytes and 1.2 nodes for keys that shared their start (bergdb 024-08, section 8). Keep
 * keys short, put large data in values, and let keys that are written together share their
 * start.</p>
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
     * <p>If key replace is enabled, each "${transactionTime}" in the key of a put is replaced
     * by the time of the transaction (Transaction.getTime()) when it is executed: its clock
     * units (Time.units()) as 18 decimal digits with leading zeros, such as
     * "/events/017942246172270000" (bergdb 020-24-01, U1-3). A time has at most 17 digits,
     * so keys that differ only in the replaced text are in the order of their transactions'
     * times. It holds for each put of the connection: put(), the puts of a WBuilder from
     * w(), and those of an rw() action, RwEnvironment.put() (020-24-02, I-6). The setting is
     * read when put(), w() or rw() is called: a change after w() does not change that
     * builder's puts. A delete's key is taken as written
     * (bergdb 019-15). In an object key (no suffix, or ".obj"), "${transactionTime}" may
     * be in the name only, the part after the last '/': a put with it in the directory
     * throws IllegalArgumentException, as the indexes of the directory that the put lands
     * in would not be known before the transaction's time (bergdb 020-14, X1). A key with
     * another suffix is never indexed, and is replaced anywhere.</p>
     *
     * <p>The transaction time of the transaction functions as a unique transaction ID.
     * It is guaranteed to be unique for every transaction and is strictly increasing. So the
     * puts of one transaction at a key with "${transactionTime}" are puts at one key, and the
     * last of them counts: a transaction that puts two such values needs another part in each
     * key, such as "${transactionTime}-1" (bergdb 020-24-01, U1-6). A transaction that also
     * puts or deletes the key that the replace gives, the time written out, would set one key
     * twice: it is refused at the commit with a DbException, nothing of it written, and the
     * database goes on (bergdb 024-16; WBuilder.execute(), rw()). A transaction has one
     * operation a key.</p>
     *
     * <p>By default, the key replace feature of a connection is disabled, also for the
     * connection that Database.connection() gives a thread until it is enabled there. This
     * method must be called to enable it. Disabled, "${transactionTime}" is a part of the key
     * as any other: three puts at "/events/${transactionTime}" put the one key
     * "/events/${transactionTime}", each over the last (bergdb 020-24-01, U1-4).</p>
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
     * A read at lookup time t reads the state that the transactions of time t and earlier
     * made: the transaction whose time is t (Transaction.getTime()) is part of it, and a read
     * at one unit before t does not see it (bergdb 020-24-01, U1-7).
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
     * @throws IllegalArgumentException
     *            If lookupTime is null (bergdb 020-24-01, U1-12).
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
     * until setLookupTime() or this method is called again (bergdb 020-10, section 3.6).
     * Each call freezes anew, at the latest state as of the next read, also after
     * setLookupTime(t): it does not freeze t (bergdb 018-04, Q2).
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
     * <p>These promises are for this started database: a time that currentTime() returned
     * holds for the session that returned it. After a restart, with a clock that stands
     * still (a test clock) or was set back, a transaction can get a time at or before a time
     * that currentTime() returned before the restart, and a read at that time then sees that
     * transaction (bergdb 018-04, Q5; 028-74). A time that holds across restarts is the time
     * of a transaction that was committed and is durable (Transaction.getTime(), after
     * Transaction.sync()): every later transaction, also after a restart, gets a later
     * time.</p>
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
     *             Thrown if the database is faulty; IllegalDbStateException if it is
     *             stopping or stopped, which is no failure (Database.stop()).
     * @throws DbFailedException
     *             If the database has failed, before or in this read (a read that fails
     *             on the storage fails it): it then refuses every transaction and read
     *             until it is restarted. See Database.
     * @throws LookupTimeNotAvailableException
     *             As for get(): the lookup time is before the first available lookup time,
     *             or became so while the read ran.
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
     * <p>A primitive class or its wrapper, such as int.class or Integer.class, reads the
     * field "p" of the stored object, where a put of a wrapper stores it, and an array class
     * other than byte[] the field "array", converted to the class. It reads that field of any
     * stored object, so an object of a Data Object class with a field named "p" reads as that
     * field's value. If the stored object has no such field, the get gives null, as for a key
     * without an entry (bergdb 020-09, section 5.9; 020-24-12, U12-7).</p>
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
     *             Thrown if the database is faulty; IllegalDbStateException if it is
     *             stopping or stopped, which is no failure (Database.stop()).
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
     * @throws LookupTimeNotAvailableException
     *             If the connection's lookup time is before the first available lookup time
     *             (Database.getFirstAvailableLookupTime()), or became so while the read ran,
     *             a cut overtaking it (setLookupTime(); bergdb 020-24-06, U6-6): the read is
     *             refused, and the database goes on. The exception is an
     *             IllegalArgumentException, so a catch of that, for a bad key, catches it
     *             too.
     * @return The object created based on 'clazz' and the data in the database,
     *             or null if there is no entry for the key; for a primitive, a wrapper or
     *             an array class, also if the stored object has no field "p" or "array".
     */
    public <TYPE> TYPE get(String key, Class<TYPE> clazz);
    
    /**
     * Returns information about the transaction that wrote the last
     * value retrieved with the get() method: its time and its KVs. The KVs
     * are the user's; those that the database writes itself in the
     * transaction, the entries of an index, are left out, and so are those at
     * a key that is no key of this API, which only a write through the Core's
     * Db makes (bergdb 020-22, R22-1).
     * A get() that finds no entry does not change the value this method describes:
     * after one, it describes the value retrieved by an earlier get().
     * An exists() of this connection counts as a get() here: one that finds the key as
     * a get() that retrieved its value, one that does not as a get() that found no entry.
     * A get() whose conversion runs a Data Object constructor that reads through this
     * connection is described, not the constructor's reads (bergdb 020-24-11, U11-5).
     * This method call will always require a read from the database
     * storage, no caching for this query.
     *
     * <p>With a finite retain duration (Database.setRetainDuration()), reclaim rewrites live
     * values, in transactions of its own, so that it can cut the front of the stream, and a
     * get then reads reclaim's copy. This method gives the transaction that wrote the value
     * even so, not reclaim's (bergdb 021-17): always when its time is at or after the first
     * available lookup time (Database.getFirstAvailableLookupTime()). A transaction before
     * that time is given only while reclaim has neither removed it nor rewritten the value
     * at or before that time.</p>
     *
     * <p>No call lists the versions of a key; a walk gives them, newest first: a get(), then
     * this method's time() t, then a get() at the lookup time Time.units(t.units() - 1), the
     * state just before that transaction, and so on, until a get() finds no value: at the
     * key's first put, or at a delete. No call gives a delete's time, so the walk stops
     * there; a get() at a lookup time before the delete goes on. Each step reads the storage
     * for this method, and the walk sets the lookup time, so use a connection of its own
     * (Database.newConnection()); with a finite retain duration the walk ends with
     * LookupTimeNotAvailableException at the first available lookup time (bergdb 020-24-05,
     * U5-11).</p>
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
     *             If the transaction that wrote the value is no longer available: its time
     *             is before the first available lookup time, and reclaim has removed it, or
     *             rewrote the value at or before that time and may remove it at any time.
     *             The value stays readable; a get at a later lookup time leads to the same
     *             refusal.
     * @throws DbException
     *             If the record of the value is malformed internal data: its value node
     *             has reclaim's copy mark, but is no copy of reclaim's, which only a damaged
     *             stream holds (bergdb 021-17, 031-06). The database goes on.
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
     *            {@linkplain bergdb.pub##objects Objects}). A put of a large object needs
     *            heap of about 4 to 5 times its stored size while it runs; an
     *            OutOfMemoryError in its transaction fails the database (the same).
     * @throws DbException
     *             If the transaction is refused, nothing of it written, and the database
     *             goes on (DbException): it passes a limit of a transaction, 500
     *             operations, 56 KiB of keys or 32 MiB of keys and values (the package's
     *             {@linkplain bergdb.pub##limits Limits}; bergdb 024-17); it is too large
     *             for a record, its values and keys taking more
     *             than 7/8 of 2^31 - 9 bytes, rounded down, 1,879,048,178 bytes, about 1.88
     *             GB, in the stream (bergdb 005-17); or the database is stopping or stopped
     *             (IllegalDbStateException). The size counts each key-value pair of the
     *             transaction, the entries of the indexes that its puts make among them: a
     *             put counts its value's bytes and 28 bytes, a delete 24 bytes, and each its
     *             key, 8 bytes for each whole 7 bytes of the key and 8 more, the key's bytes
     *             being its UTF-8 and one more for each '/'; each pair rounded up to a
     *             multiple of 4. So a pair with a key of up to 30 bytes counts 30 to 45
     *             bytes more than its key and its value (bergdb 020-24-13, U13-2). Or if
     *             the thread is interrupted while the transaction waits to run again after
     *             a conflict, which a put at an object key may meet, as it runs as an rw()
     *             does (bergdb 020-10, section 5.1): it is not run, and the thread's
     *             interrupt flag is set (Database, "Interrupts").
     * @throws DbFailedException
     *             If the database has failed, in this transaction or before: it then
     *             refuses every transaction and read until it is restarted. See
     *             Database.
     * @throws IllegalArgumentException
     *             If 'key' is null or otherwise invalid, or if object is null; or if it
     *             is a String with a lone surrogate, or an object with a string that has
     *             one, as for WBuilder.put() (the package's
     *             {@linkplain bergdb.pub##strings Strings}; bergdb 019-44, 021-04); or if
     *             the object cannot be stored exactly, as for WBuilder.put(); or if the key
     *             or the value passes its limit (L2, L4), as for WBuilder.put(), or the
     *             object's levels for an index of its directory take more than 111 bytes
     *             (L6), as for WBuilder.execute() (the package's
     *             {@linkplain bergdb.pub##limits Limits}).
     * @throws DataFormatException
     *             If it puts a byte[] that is an object of BergDB 2026.3 and before (format
     *             1) at an object key of a directory with a user index, which no index can
     *             take (IndexBuilder, rule 1): nothing is written, and the database goes on.
     */
    public Transaction put(String key, Object object);

    /**
     * Deletes a key-value entry from the database. If no entry has the key, nothing is
     * deleted, but the delete is still a transaction of its own, with a time of its own,
     * which this method commits and returns, as for a key with an entry. The value stays
     * readable at earlier lookup times, as every earlier state, until reclaim cuts them
     * (Database.setRetainDuration()), and with the default retain duration forever: a delete
     * does not erase a key's history (bergdb 020-24-01, U1-11).
     * 
     * @param key
     *             The key of the key-value entry. Must begin with "/".
     * @throws DbException
     *             If the transaction is refused, as for put(); or if the thread is
     *             interrupted while the transaction waits to run again after a conflict,
     *             which a delete at an object key may meet, as a put there: it is not run,
     *             and the thread's interrupt flag is set (Database, "Interrupts").
     * @throws DbFailedException
     *             If the database has failed, in this transaction or before: it then
     *             refuses every transaction and read until it is restarted. See
     *             Database.
     * @throws IllegalArgumentException
     *             If 'key' is null or otherwise invalid, or has more than 111 bytes as
     *             stored (L2; the package's {@linkplain bergdb.pub##limits Limits}).
     */
    public Transaction delete(String key);   

    /**
     * Creates a builder object used to build a write-only transaction: a new builder at each
     * call, for one transaction, as execute() spends it (WBuilder).
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
     * <p>A call of a Connection or of the Database inside the action is not part of the
     * transaction: it is a transaction of its own, committed at once, not undone, and made
     * again at each run. One that writes what the action read makes rw() run the action
     * again and again, until the thread is interrupted or the database stops (Action.run();
     * bergdb 020-24-11, U11-4).</p>
     * 
     * <p>What the action throws, other than an Error, rw() throws as it is, a checked
     * exception too, and nothing is written (Action.run()).</p>
     * 
     * @throws IllegalArgumentException
     *             If action is null; or after the action, if it put an object whose levels
     *             for an index of its directory take more than 111 bytes (L6; the package's
     *             {@linkplain bergdb.pub##limits Limits}), as for WBuilder.execute():
     *             nothing is written.
     * @throws DbException
     *             If the transaction is refused, as for put(), also when the database stops
     *             while the action runs (Database.stop()), or as for WBuilder.execute():
     *             key replace makes two of its keys one key; or if the thread is
     *             interrupted while the transaction waits to run again after a conflict:
     *             it is not run, and the thread's interrupt flag is set (Database,
     *             "Interrupts").
     * @throws DbFailedException
     *             If the database has failed, in this transaction or before: it then
     *             refuses every transaction and read until it is restarted. See
     *             Database.
     * @throws DataFormatException
     *             If the action puts a byte[] that is an object of BergDB 2026.3 and
     *             before (format 1) at an object key of a directory with a user index, which
     *             no index can take (IndexBuilder, rule 1): nothing is written, and the
     *             database goes on.
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
     *             If 'indexName' or 'type' is null; or if 'type' is String.class, whatever
     *             the data: an index's values are objects, which a get does not give as a
     *             String (bergdb 020-21, 3).
     * @throws LookupTimeNotAvailableException
     *             If the lookup time is before Database.getFirstAvailableLookupTime(): the
     *             index's definition cannot be read at it.
     * @throws bergdb.pub.util.IllegalDbStateException
     *             If the database is stopping or stopped (Database.stop()).
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
     *             it waits: the transaction stays committed (see Database.sync()); or if the
     *             database stops before the transaction is durable, as for Database.sync().
     * @throws DbFailedException
     *             If the storage has failed: the database fails. See Database.
     */
    public void sync();

    /**
     * Waits until the specified sync level (durability) has been achieved 
     * for the last transaction started with this connection.
     *
     * @throws DbException if the database is faulty, or if the thread is interrupted while
     *             it waits, as for sync().
     * @throws DbFailedException
     *             If the storage has failed: the database fails. See Database.
     * @throws IllegalArgumentException If syncLevel is null (bergdb 020-25).
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