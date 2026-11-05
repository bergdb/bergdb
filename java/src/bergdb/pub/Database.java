package bergdb.pub;

import bergdb.common.Util;
import bergdb.pub.util.DbException;
import bergdb.pub.util.DbFailedException;
import bergdb.pub.util.IllegalDbStateException;
import bergdb.pub.util.Job;
import bergdb.pub.util.SyncLevel;

/**
 * <p>A representation of a started BergDB database.</p>
 * 
 * <p>Multiple Database instances representing the same database (same storage location) should 
 * be avoided.
 * </p>
 * 
 * <p>A transaction that the database refuses, such as one that is too large, changes nothing,
 * and the database goes on. A transaction that fails after it began fails the database: the
 * storage, the JVM or memory failed (an I/O error, a corrupt stream, an OutOfMemoryError), or
 * there is a bug. Nothing is rolled back. The call throws a DbFailedException with what
 * failed as the cause (an Error is thrown as it is), and every later transaction and read
 * throws one too, until the database is restarted: stop it and start it again. The restart
 * rebuilds the database from its storage, as after a crash: the failed transaction is there
 * if it was written before the failure, and otherwise not. An in-memory database is lost.
 * sync() still works for the transactions before the failure.</p>
 *
 * <p>A read or a sync that fails on the storage (an I/O error, corrupt data) fails the
 * database in the same way: the call throws a DbFailedException with the failure as the
 * cause, and so does every later transaction and read until the restart (bergdb 005-30).
 * A read whose lookup time has expired throws LookupTimeNotAvailableException instead, and
 * the database goes on (see getFirstAvailableLookupTime()).</p>
 * 
 * <p>Interrupts (bergdb 005-46). An interrupt of the calling thread never fails the
 * database. Three calls only wait, and an interrupt ends the wait: sync() throws a
 * DbException, and the transaction stays committed; a Job's join() returns the job's
 * status; and a transaction that waits to run again after a conflict throws a DbException,
 * not run. Every other call ignores an interrupt until it is done. Either way, the
 * thread's interrupt flag is set when the call returns or throws, if it was set before or
 * during the call.</p>
 * 
 * <p>Stop or close each Database that is started, as a file: nothing else stops it (bergdb
 * 005-55). stop() returns at once; close() waits until the database is closed. Database is
 * AutoCloseable (bergdb 005-59), so a try-with-resources block closes it when the block ends,
 * also when the block throws:</p>
 * <pre>
 * try (Database db = Factory.database().memory().start()) {
 *     db.connection().w().put("/key", "value").execute();
 * }
 * </pre>
 * 
 * @author Frans Lundberg
 */
public interface Database extends AutoCloseable {

    /**
     * Name of the primary index.
     *
     * <p>Experimental in 2026.3, with known faults; it may change in a later release
     * (bergdb 018-01, D6).</p>
     */
    public static final String PRIMARY = Util.identity("primary");

    /**
     * Returns information about the startup of this database.
     */
    public StartupInfo getStartupInfo();

    /**
     * <p>Stops the database and closes it properly, without waiting (bergdb 005-35): no
     * transaction or read starts after this method, and a transaction that runs completes.
     * Every transaction that has returned is then written and the files are closed, in the
     * background, typically within a second, also when the program returns from main right
     * after this method. This method returns at once; close() also waits until the database
     * is closed. Until 005-35, what was still buffered was lost.
     * Call close() to wait for completion and report a failed flush or storage close
     * (bergdb 005-73, F5).
     * </p>
     * 
     * <p>Call sync() before stop() when the transactions must be durable when stop()
     * returns: with a file storage, sync() waits until they are forced to the device. After
     * this method has been called this Database object must not be used anymore. This method
     * is OK to call multiple times from multiple unsynchronized threads; only the first call
     * to this method has any effect (idempotent method).
     * </p>
     * 
     * <p>stop() or close() must be called once the Database is no longer used, as close() for
     * a file or a socket: nothing else stops it (2026-10-27, bergdb 005-55; until then the
     * garbage collector stopped a Database that nothing referred to). A Database that is not
     * stopped keeps its storage threads, its open files, its write buffer and its memory until
     * the JVM exits. What it has committed is still written within the buffer time, as after any
     * commit; at the exit of the JVM, what is buffered and not yet written is lost, as in a
     * crash, which the database tolerates.
     * </p>
     * 
     * <p>Start another database on the same directory only after this one is closed, when
     * close() has returned (bergdb 005-63). Until then, a start there is refused:
     * DatabaseBuilder.start() throws.
     * </p>
     */
    public void stop();
    
    /**
     * <p>Stops the database as stop() does, and waits until it is closed (bergdb 005-59):
     * every transaction that has returned is written, with a file storage forced to the
     * device, the files are closed, and the storage threads have ended; also when stop() or
     * another close() began the close. After this method has been called this Database object
     * must not be used anymore. It is safe to call it several times, also after stop(), and
     * from different threads.
     * </p>
     * 
     * <p>This is AutoCloseable's close(), without its checked exception: a try-with-resources
     * block calls it when the block ends, also when the block throws.
     * A failed final flush or storage close throws StreamIoException, also after stop()
     * or an earlier close() (bergdb 005-73, F5).
     * </p>
     */
    public void close();

    /**
     * Gets a connection to the database. The returned object is always the same object for one
     * specific thread that calls this method. Two different threads calling this method are
     * guaranteed to get different Connection instances. Each call sets the requested lookup
     * time of the returned Connection to Time.MAX, the latest state (Connection.setLookupTime()).
     */
    public Connection connection();

    /**
     * Creates and returns a new connection to the database. The returned object is always newly
     * created in this method and is guaranteed not to be returned from subsequent calls to
     * newConnection() or connection(). Its requested lookup time is Time.MAX, the latest state
     * (Connection.setLookupTime()).
     */
    public Connection newConnection();

    /**
     * Waits until the last started transaction has been stored durably according to the ordinary
     * durability rules.
     * 
     * @throws DbException
     *             if the database is faulty, or if the thread is interrupted while it waits
     *             (a StreamIoException whose cause is an InterruptedIOException): the
     *             transaction stays committed, the database goes on, and the thread's interrupt
     *             flag is set (bergdb 005-46).
     * @throws DbFailedException
     *             If the storage has failed: the database fails (see above).
     */
    public void sync();
    
    /**
     * Waits until the last started transaction has been stored durably according to the
     * specified sync level.
     * 
     * @throws DbException
     *             if the database is faulty, or if the thread is interrupted while it waits,
     *             as for sync().
     * @throws DbFailedException
     *             If the storage has failed: the database fails (see above).
     */
    public void sync(SyncLevel syncLevel);

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
     * Returns the minimum duration for which data should be available for historic lookups.
     */
    public Duration getRetainDuration();

    /**
     * <p>
     * Sets the retain duration of the database. The retain duration is the amount of time that
     * historic data states should stay available for lookup operations. This method can be called
     * before start() or while the database is running.
     * </p>
     * 
     * <p>
     * If the retain duration is increased, the actual duration available for lookups will increase
     * until it equals or exceeds the retain duration set in this method. Use
     * getFirstAvailableLookupTime() to see the currently available time span for lookups.
     * </p>
     * 
     * <p>
     * A finite duration makes the database reclaim stream space: it rewrites live values that
     * are stored in the front of the stream, and then cuts the front. This costs writes and
     * space. Measured with the default settings (2026-10-13, see bergdb 011-04, "Level 3
     * cost"): when the duration is short, the write efficiency (user bytes divided by stream
     * bytes written) is 23 to 38 percent lower than without reclaim, and the stream kept is
     * several times the data accessible within the duration (store efficiency 0.09 to 0.75,
     * depending on value size and update pattern). The cost is lower for a long duration.
     * </p>
     *
     * <p>
     * Use Duration.MAX to keep old states available forever. Note, that this will increase the
     * database storage space indefinitely even when data is deleted from the database. This could
     * be a valid setting however. The retain duration can be decreased later, also while the
     * database is running.
     * </p>
     * 
     * @param duration
     *            The duration to retain historic data states available for lookup operations.
     */
    public void setRetainDuration(Duration duration);

    /**
     * <p>Returns the startup distance setting in MB (mega = 1000000, rounded): the target
     * size of the startup section, not the section's present length.</p>
     */
    public int getStartupDistanceInMb();

    /**
     * <p>Sets the startup distance, the target size of the startup section: the part of the
     * stream that a start reads (bergdb 005-49), while the database runs (bergdb 005-53).
     * The value is clamped as DatabaseBuilder.startupDistanceInMb() clamps it, to 5 to 1000
     * MB. The new setting is in force when the method returns. It is written to the stream
     * with a small transaction of the database's own (a value of 200 kB), so a restart keeps
     * it, as it keeps the setting the database was created with; a call with the setting in
     * force writes nothing. A setting that changes the stream's bytes, as this one does, is
     * kept in the stream; one that does not, as the cache size, lasts for the run.</p>
     *
     * <p>The startup section follows the setting as transactions are committed: after a
     * decrease, each commit writes more of the index, in proportion to its size, and no
     * commit writes the whole of it; the section is near the new setting after stream of
     * about 1.4 times the index changed since the startup position (bergdb 007-06, 007-07).
     * Without commits it does not move. After an increase, commits write less of the index
     * until the section has grown to the setting. A larger distance writes fewer bytes a put
     * and starts more slowly.</p>
     *
     * @param startupDistanceInMb  The startup distance in megabytes (mega = 1000000).
     * @throws IllegalDbStateException  If the database is stopping or stopped, as a
     *     transaction does; the setting is then unchanged.
     * @throws DbFailedException  If the database has failed, as a transaction does.
     */
    public void setStartupDistanceInMb(int startupDistanceInMb);

    /**
     * <p>Returns the cache size setting in MB (mega = 1000000, rounded): the budget of the
     * database's cache, not the memory the cache holds now.</p>
     */
    public int getCacheSizeInMb();

    /**
     * <p>Sets the cache size indicator in MB, the budget of the database's cache, while the
     * database runs (bergdb 005-52), as DatabaseBuilder.cacheSizeInMb() does at start,
     * clamped the same way, to 4 to 100,000 MB. The new budget is in force when the method
     * returns. After a decrease the database evicts what it holds above the budget in
     * batches of at most 2 ms, which this call and the database's commits and reads start,
     * until the memory it holds is at most the budget, also if no call follows; reads may
     * wait for a batch meanwhile, at most 2 ms each. A commit's own reads of the keys it
     * writes do not wait, and the commit runs one batch at its end (bergdb 005-52); the
     * memory held may rise by what those reads load until then. What the database must keep
     * in memory (the nodes changed since its startup position) is never evicted and may
     * exceed the budget. After an increase, the cache grows as data is read.</p>
     *
     * <p>The setting is for this run only: it changes no byte of the stream, so it is not
     * kept there, and a restart takes the builder's value, or its default, a fifth of the
     * JVM's maximum heap. A setting that changes the stream's bytes, as the startup distance,
     * is kept in the stream; one that does not lasts for the run. After stop() the method
     * has no effect.</p>
     *
     * @param cacheSizeInMb  The cache size indicator in megabytes (mega = 1000000).
     */
    public void setCacheSizeInMb(int cacheSizeInMb);

    /**
     * <p>
     * Returns the first (earliest) lookup time that is currently available for making a lookup (get
     * operation).
     * </p>
     *
     * <p>
     * The time only moves forward, and only when the database reclaims old data (the retain
     * duration is finite). A read at an earlier lookup time throws
     * LookupTimeNotAvailableException. The time can move while a read is running: a read that was
     * accepted may then fail with the same exception, if it needs data that was removed; the
     * database and other reads are not affected. The database guarantees that lookups work for
     * every time in [now - retain duration, now] when the time is moved; a read that runs longer
     * than that may expire. Retry such a read with a later lookup time.
     * </p>
     */
    public Time getFirstAvailableLookupTime();

    /**
     * Returns an IndexBuilder used to create a secondary index.
     *
     * <p>Experimental in 2026.3, with known faults; it may change in a later release
     * (bergdb 018-01, D6).</p>
     * 
     * @param indexName
     *            Unique name of the index. Cannot be the empty string. Cannot contain the forward
     *            slash character (/), or a whitespace character.
     * @throws IllegalArgumentException
     *             If 'indexName' is illegal.
     * @throws IndexAlreadyExistsException
     *             If an index with the given name already exists.
     */
    public IndexBuilder indexBuilder(String indexName);

    /**
     * Starts and returns a Job that deletes an index in the background.
     * If a job that deletes the index runs already, returns that job.
     *
     * <p>Experimental in 2026.3, with known faults; it may change in a later release
     * (bergdb 018-01, D6).</p>
     * 
     * @param indexName
     *            Unique name of the index.
     * @throws NoSuchIndexException
     *             if there is not index with the given name.
     */
    public Job deleteIndex(String indexName);
}
