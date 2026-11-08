package bergdb.pub.util;

/**
 * The build of a user index, in this process (bergdb 020-10, section 3.2): from
 * IndexBuilder.start(), or from Database.indexJob(name).
 * 
 * @author Frans Lundberg
 */
public interface Job {
    
    /**
     * The status now: a snapshot, immutable, all its values taken at this call (bergdb
     * 015-39).
     */
    public JobStatus getStatus();
    
    /**
     * Waits until the build ends in this process: the status is then ACTIVE or FAILED, or
     * BUILDING if the database stopped (the next start takes the build again). If the build
     * ended already, returns at once. An interrupt of the calling thread ends the wait: the
     * method returns the status, the build goes on, and the thread's interrupt flag is set
     * (bergdb 005-46).
     */
    public JobStatus join();
    
    /**
     * As join(), but waits at most 'millis' milliseconds; 0 waits as join().
     */
    public JobStatus join(int millis);
}
