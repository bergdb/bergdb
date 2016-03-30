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
     * Returns the first (earliest) lookup time that is currently available for making a lookup (get
     * operation).
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
