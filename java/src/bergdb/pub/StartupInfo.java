package bergdb.pub;

import bergdb.pub.util.Job;

/**
 * Immutable information about the start of the database.
 * 
 * @author Frans Lundberg
 */
public interface StartupInfo {
    
    /**
     * Returns the startup jobs if any: the jobs of the user indexes that the start resumed.
     *
     * <p>Experimental in 2026.3, with known faults; it may change in a later release
     * (bergdb 018-01, D6).</p>
     */
    public Job[] getStartupJobs();
    
    /**
     * Returns the number of seconds it took to start the database.
     */
    public double getStartupDuration();
}
