package bergdb.pub;

import java.util.List;

// TODO A. Use this class!

/**
 * An object of this class represents a database that has not yet
 * been started.
 * 
 * @author Frans Lundberg
 */
public interface UnstartedDatabase {

    /**
     * Starts the database and returns a Database object.
     * 
     * @throws IllegalStateException
     *             If start() has been called already.
     * @throws DbException
     *             If the database is not functioning.
     * @throws BadReplicaException
     *             If the replica provided in when creating the Database object
     *             is not a valid replica of the database. The database ID in
     *             the stream may be wrong, for example.
     */
    public Database start();

    /**
     * @return A list of internal jobs started by the start() method. 
     * Jobs include finishing the creation of an index or finishing the deletion of an index.
     */
    public List<Job> getStartJobs();
}
