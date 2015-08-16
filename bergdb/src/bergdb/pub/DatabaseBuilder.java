package bergdb.pub;

import java.io.IOException;

/**
 * A DatabaseBuilder is used to create a Database.
 * Use the settings methods (dir, memory, replica, clock, ...) and then 
 * call start() to create and start the database.
 * 
 * @see Database
 * @author Frans Lundberg
 */
public interface DatabaseBuilder {
    
    /**
     * Use the given directory to store the database stream in files.
     * 
     * @throws DbException  If there is file error when accessing the 
     * specified directory.
     */
    public DatabaseBuilder dir(String dirname);
    
    /**
     * An in-memory database stream will be used.
     * This option may be suitable for testing.
     */
    public DatabaseBuilder memory();
    
    /**
     * Provide a CryptoKey to use an existing encrypted database, or start a
     * new one using the provided encryption key.
     * 
     * @param cryptoKey  
     *      The crypto key to use or CryptoKey.NULL to not use any encryption.
     */
    public DatabaseBuilder cryptoKey(CryptoKey cryptoKey);
    
    /**
     * Adds a replica to the sets of database replicas.
     * 
     * @param name  Name of the storage replica.
     * @param dir   Directory of the replica database data.
     * @throws IOException  if there is a file access error with the specified directory 'dir'.
     */
    public DatabaseBuilder replica(String name, String dir) throws IOException;
    
    /**
     * Sets a non-default database clock. Use this method together with a TestClock to do
     * deterministic testing.
     */
    public DatabaseBuilder clock(Clock clock);
    
    /**
     * Sets the wanted retain duration.
     */
    public DatabaseBuilder retainDuration(Duration duration);
    
    /**
     * Sets the startup distance to a non-default value.
     * A small startup distance can decrease database startup time; while a larger
     * startup distance can improve the overall database performance.
     * For a low-end PC with 0.5 GB of RAM, a value of 5 is reasonable, while a 
     * high-end server may use 50.
     * The value should be seen as a proposal, if the database considers the value
     * too small or to high, it may clamp it to an internally permitted range.
     * 
     * @param startupDistanceInMb    The startup distance in megabytes (mega = 1000000). 
     *                               Value should be between 5 and 100.
     */
    public DatabaseBuilder startupDistanceInMb(int startupDistanceInMb);
    
    /**
     * Sets the target database cache size.
     * A small value will leave more available memory for the rest of the JVM application;
     * a larget value improves that database performance.
     * 
     * @param cacheTargetSizeInMb  The target cache size in megabytes (mega = 1000000).
     */
    public DatabaseBuilder targetCacheSizeInMb(int cacheTargetSizeInMb);

    /**
     * Starts the database. When this method returns, connections to the
     * database can be made.
     * 
     * @throws DbException
     *             If a functioning database could not be started.
     * @throws BadReplicaException
     *             If the replica provided when creating the Database object
     *             is not a valid replica of the database. The database ID in
     *             the stream may be wrong, for example.
     * @throws BadCryptoKey
     *             If the wrong crypto key is used, or none is used with an encrypted
     *             database or a crypto key is used with an unencrypted database.
     */
    public abstract Database start();
}
