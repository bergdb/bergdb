package bergdb.pub;

import java.io.IOException;

/**
 * A DatabaseBuilder is used to create a database.
 * Use the settings methods (dir, memory, replica, clock) and then build() to create the Database.
 * start() is a convenience shortcut to create and start the Database in one method call.
 * 
 * @author Frans Lundberg
 */
public interface DatabaseBuilder {
    
    // TODO D. Consider: Should we really through IOException. We usually throw 
    // subclasses of RuntimeException.
    
    /**
     * Use the given directory to store the database stream in files.
     * 
     * @throws IOException f there is a file access error with the specified directory 'dirname'.
     */
    public DatabaseBuilder dir(String dirname) throws IOException;
    
    /**
     * An in-memory database stream will be used.
     * This option may be suitable for testing.
     */
    public DatabaseBuilder memory();
    
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
     * Starts the database. When this method returns, connections to the
     * database can be made.
     * 
     * @throws DbException
     *             If the database is not functioning.
     * @throws BadReplicaException
     *             If the replica provided in when creating the Database object
     *             is not a valid replica of the database. The database ID in
     *             the stream may be wrong, for example.
     */
    public abstract Database start();
        
    // TODO Add setRetainDuration to this builder.
}
