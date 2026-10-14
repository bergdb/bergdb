package bergdb.pub.util;

/**
 * An instance of this class represents a long-running 
 * job performed in the background.
 * 
 * @author Frans Lundberg
 */
public interface Job {
    
    /**
     * Returns the current status of the job.
     * The returned object is immutable.
     */
    public JobStatus getStatus();
    
    /**
     * Waits indefinitely for the job to finish in another thread.
     * If the job has finished already, this method returns immediately.
     */
    public JobStatus join();
    
    /**
     * Waits at most 'millis' milliseconds for the job to finish in another thread.
     * If the job finished already, this method returns immediately.
     * 
     * @param millis  The maximum time to wait in milliseconds.
     * A 'millis' value of 0 means to wait forever.
     */
    public JobStatus join(int millis);
}
