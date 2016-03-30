package bergdb.pub.util;

/**
 * Job status, implementations must be immutable.
 * 
 * @see Job
 * @author Frans Lundberg
 */
public interface JobStatus {
    
    /**
     * Returns the progress value. -1 means "unknown progress", 
     * a value between 0 and 99 roughly corresponds to percentage completed, and
     * 100 means "finished"
     */
    public int progress();
    
    /**
     * A human-readable string in English describing the status of the Job.
     */
    public String note();
}
