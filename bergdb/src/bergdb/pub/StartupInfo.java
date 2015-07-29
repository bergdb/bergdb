package bergdb.pub;

/**
 * Immutable information about the start of the database.
 * 
 * @author Frans Lundberg
 */
public interface StartupInfo {
    
    // TODO D. Add wasCreated().
    // TODO D. Add getDatabaseId() [if not available from Db directly]
    
    
    /**
     * Returns the startup jobs if any.
     */
    public Job[] getStartupJobs();
    
    /**
     * Returns the number of seconds it took to start the database.
     */
    public double getStartupDuration();
    
}
