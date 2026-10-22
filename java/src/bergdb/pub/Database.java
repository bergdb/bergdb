package bergdb.pub;

import java.io.IOException;

import bergdb.core.SyncLevel;
import bergdb.pub.util.BadReplicaException;
import bergdb.pub.util.DbException;
import bergdb.pub.util.Job;
import bergdb.pub.util.StorageInfo;
import bergdb.pubimp.IndexManager;

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
 * @author Frans Lundberg
 */
public interface Database {

    /**
     * Name of the primary index.
     */
    public static final String PRIMARY = IndexManager.PRIMARY;

    /**
     * Returns information about the startup of this database.
     */
    public StartupInfo getStartupInfo();

    /**
     * <p>Stops the database - requests that resources allocated by this Database are eventually
     * released. This method returns quickly. It does not wait until resources have been released;
     * this will happen asynchronously in the background. Typically, resources are released within
     * one second after this method has been called.
     * </p>
     * 
     * <p>The user of this class should call sync() before stop() when appropriate; this method does
     * not call sync(). After this method has been called this Database object must not be used
     * anymore. This method is OK to call multiple times from multiple unsynchronized threads; only
     * the first call to this method has any effect (idempotent method).
     * </p>
     * 
     * <p>It is not a requirement that stop() is called once the Database is not longer used. If there
     * are no references to this Database object or to any Connection or Transaction object created
     * with this Database, the Database will be stopped automatically when garbage collected.
     * However, since the programmer has little control over when Java garbage collection actually
     * occurs, it may be beneficial to call stop() to free resources sooner.
     * </p>
     */
    public void stop();

    /**
     * Gets a connection to the database. The returned object is always the same object for one
     * specific thread that calls this method. Two different threads calling this method are
     * guaranteed to get different Connection instances. The lookupTime of the returned Connection
     * is always Long.MAX_VALUE.
     */
    public Connection connection();

    /**
     * Creates and returns a new connection to the database. The returned object is always newly
     * created in this method and is guaranteed not to be returned from subsequent calls to
     * newConnection() or connection().
     */
    public Connection newConnection();

    /**
     * Waits until the last started transaction has been stored durably according to the ordinary
     * durability rules.
     * 
     * @throws DbException
     *             if the database is faulty.
     */
    public void sync();
    
    /**
     * Waits until the last started transaction has been stored durably according to the
     * specified sync level.
     * 
     * @throws DbException
     *             if the database is faulty.
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
     * <p>
     * 
     * <p>
     * A finite duration makes the database reclaim stream space: it rewrites live values that
     * are stored in the front of the stream, and then cuts the front. This costs writes and
     * space. Measured with the default settings (2026-10-13, see docs/levels.md, "Level 3
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
     * 
     * @param indexName
     *            Unique name of the index.
     * @throws NoSuchIndexException
     *             if there is not index with the given name.
     */
    public Job deleteIndex(String indexName);

    /**
     * Adds a replica storage to this database while it is running. The replicated data is storage
     * in the provided directory.
     * 
     * @param name
     *            Name of the storage to add.
     * @param dir
     *            Directory where to store the replica. May have previous existing data of this
     *            database.
     * @throws IOException
     *             If the directory does not exist and cannot be created or if the database file in
     *             the directory cannot be opened, or any other file access problem.
     * @throws BadReplicaException
     *             If the replica stream is longer than the main stream; if the replica stream has a
     *             different database ID than the main stream.
     */
    public Job addReplica(String name, String dir) throws IOException;

    /**
     * Removes a replica storage from the database. The existing replica data is not deleted but
     * will no longer be updated.
     * 
     * @param name
     *            Name of the storage.
     */
    public void removeReplica(String name);

    /**
     * Returns information about the storages currently used by the database.
     */
    // NOTE Consider making the returned data immutable? Or not? Should it be used for
    // custom durability rules?
    public StorageInfo[] getStorageInfos();
}
