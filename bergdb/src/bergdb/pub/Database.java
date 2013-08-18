package bergdb.pub;

import java.io.IOException;
import java.util.List;

import bergdb.pubimp.IndexManager;

/**
 * <p>A representation of a BergDB database. Call start() before any other methods.</p>
 * 
 * <p>Multiple Database objects in the same process representing the same database
 * should be avoided.</p>
 * 
 * @author Frans Lundberg
 */
public interface Database {
    
    /**
     * Name of the primary index.
     */
    public static final String PRIMARY = IndexManager.PRIMARY;
    
    /**
     * Starts the database. When this method returns, connections to the
     * database can be made.
     * 
     * @throws IllegalStateException
     *             If start() has been called already.
     * @throws DbException
     *             If the database is not functioning.
     * @throws BadReplicaException
     *             If the replica provided in when creating the Database object
     *             is not a valid replica of the database. The database ID in
     *             the stream may be wrong, for example.
     * @return A list of internal jobs started by the method. Jobs include finishing the 
     * creation of an index or finishing the deletion of an index.
     */
    public List<Job> start();
    
    /**
     * <p>Stops the database - requests that resources allocated by this Database are 
     * eventually released. This method returns quickly. It does not wait until resources 
     * have been released; this will happen asynchronously in the background.
     * Typically, resources are released within one second after this method has been called.</p>
     * 
     * <p>The user of this class should call sync() before stop() when appropriate; this method
     * does not call sync().
     * After this method has been called the Database object cannot be used anymore.
     * This method is OK to call multiple times from multiple unsynchronized threads; only
     * the first call to this method has any effect.</p>
     * 
     * <p>It is not a requirement that stop() is called once the Database is not longer used.
     * If there are no references to this Database object or to any Connection or 
     * Transaction object created with this Database, the Database will be stopped 
     * automatically when garbage collected. However, since the programmer has little control
     * over when Java garbage collection actually occurs, it may be beneficial to call 
     * stop() to free resources sooner.</p>
     */
    public void stop();
    
    /**
     * Gets a connection to the database.
     * The returned object is always the same object for one specific thread that calls this 
     * method. Two different threads calling this method are guaranteed to get different 
     * Connection instances. The lookupTime of the returned Connection is always Long.MAX_VALUE.
     * 
     * @throws IllegalDbStateException if start() has not been called.
     */
    public Connection connection();
    
    /**
     * Gets a new connection to the database.
     * The returned object is always newly created in this method and will not be
     * returned from newConnection() or connection() again.
     * 
     * @throws IllegalDbStateException if start() has not been called.
     */
    public Connection newConnection();
    
    /**
     * Waits until the last started transaction has been stored durably.
     * 
     * @throws IllegalDbStateException if start() has not been called.
     */
    public void sync();
    
    /**
     * <p>Returns the current database time in 100 ns units. The returned time is guaranteed to be 
     * strictly less then the transaction time of any currently executing transaction (if any 
     * transaction is executing) and less then the transaction time of any future transaction.
     * The time is measured in number of 100 nanosecond units that has passed since Unix Epoch
     * (00:00:00.000 1 Jan 1970). Leap seconds are not counted; a day always has 24*60*60 seconds
     * (24*60*60*10,000,000 time units).</p>
     * 
     * <p>For testing purposes, a database clock may use another time standard.</p>
     */
    public long getTime();
    
    /**
     * Returns the minimum duration for which data should be available for historic lookups.
     * The number returned is the number of db time units (see getTime()).
     */
    public long getRetainDuration();
    
    /**
     * <p>Sets the retain duration of the database. The retain duration is the amount of time
     * that historic data states should stay available for lookup operations.
     * This method can be called before start() or while the database is running.</p>
     * 
     * <p>If the retain duration is increased, the 
     * actual duration available for lookups will increase until it exceeds the retain duration
     * set in this method. Use getFirstAvailableLookupTime() to see the currently available
     * time span for lookups.<p>
     * 
     * <p>Use Long.MAX_VALUE to keep old states available forever. Note, that this will increase
     * the database storage space indefinitely even when data is deleted from the database.
     * This could be a valid setting however. The retain duration can be decreased later, also
     * while the database is running.</p>
     * 
     * @param retainDuration  The time to retain historic data states available for
     * lookup operations. The time duration is measured in DB time units (see getTime()).
     * The value must be at least 1*Clock.UNITS_PER_SEC, a shorter retain duration is not allowed.
     */
    public void setRetainDuration(long retainDuration);
    
    /**
     * Returns the first (earliest) lookup time that is currently available for making a 
     * lookup (get operation).
     */
    public long getFirstAvailableLookupTime();
    
    /**
     * Returns an IndexBuilder used to create a secondary index.
     * 
     * @param indexName  Unique name of the index. Cannot be the empty string. Cannot contain 
     * the forward slash character (/), or a whitespace character.
     * @throws IllegalArgumentException If 'indexName' is bad.
     * @throws IndexAlreadyExistsException If an index with the given name already exists.
     */
    public IndexBuilder indexBuilder(String indexName);
    
    /**
     * Starts and returns a Job that deletes an index in the background.
     * 
     * @param indexName  Unique name of the index.
     * @throws NoSuchIndexException if there is not index with the given name.
     */
    public Job deleteIndex(String indexName);
    
    /**
     * Adds a replica storage to this database while it is running.
     * The replicated data is storage in the provided directory.
     * 
     * @param name  Name of the storage to add.
     * @param dir   Directory where to store the replica. May have previous existing data of
     *              this database.
     * @throws IOException
     *              If the directory does not exist and cannot be created or if the database file
     *              in the directory cannot be opened, or any other file access problem.
     * @throws BadReplicaException  
     *              If the replica stream is longer than the main stream; 
     *              if the replica stream has a different database ID than the main stream.
     */
    public Job addReplica(String name, String dir) throws IOException;
    
    /**
     * Removes an active replica storage from the database. The existing replica data is not 
     * deleted but will no longer be updated.
     * 
     * @param name  Name of the storage.
     */
    public void removeReplica(String name);
    
    /**
     * Returns information about the storages currently used by the database.
     */
    // NOTE Consider making the returned data immutable? Or not? Should it be used for 
    // custom durability rules?
    public StorageInfo[] getStorageInfos();
}
