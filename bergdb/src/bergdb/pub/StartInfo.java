package bergdb.pub;

/**
 * Immutable information about the start of the database.
 * 
 * @author Frans Lundberg
 */
public interface StartInfo {
    
    /**
     * Returns the start jobs.
     */
    public Job[] getStartJobs();
    
    /**
     * Returns the time it took to start the database (seconds).
     */
    public double getStartTime();
}
