package bergdb.pub;

import bergdb.pub.util.Job;

/**
 * Immutable information about the start of the database.
 * 
 * @author Frans Lundberg
 */
public interface StartupInfo {
    
    /**
     * Returns the startup jobs if any.
     */
    public Job[] getStartupJobs();
    
    /**
     * Returns the number of seconds it took to start the database.
     */
    public double getStartupDuration();
}
