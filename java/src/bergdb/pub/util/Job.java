package bergdb.pub.util;

/**
 * The build of a user index, in this process (bergdb 020-10, section 3.2): from
 * IndexBuilder.start(), or from Database.indexJob(name). join() waits until the build ends,
 * and throws IndexBuildException if the build failed, as Future.get() throws for a task that
 * failed; getStatus() never throws, and follows a build without exceptions.
 * 
 * @author Frans Lundberg
 */
public interface Job {
    
    /**
     * The status now: a snapshot, immutable, all its values taken at this call (bergdb
     * 015-39). It never throws for a failed build: the state is then FAILED, with the
     * reason.
     */
    public JobStatus getStatus();
    
    /**
     * Waits until the build ends in this process, and returns its status: ACTIVE when the
     * index is built, or BUILDING if the database stopped (the next start takes the build
     * again). If the build ended already, returns at once. An interrupt of the calling thread
     * ends the wait: the method returns the status, BUILDING while the build goes on, and the
     * thread's interrupt flag is set (bergdb 005-46).
     *
     * <p>If the build failed, the method throws IndexBuildException instead, each time it is
     * called, also on the job that Database.indexJob(name) gives later. A build fails when
     * the index was deleted while it was building, when the build met data that it cannot
     * index, such as an object of the format of BergDB 2026.3 and before, or when it met
     * another exception, a bug. The exception's status is FAILED, and its cause is the
     * exception that failed the build (none for a deletion). The database goes on; see
     * IndexBuildException. getStatus() tells of a failure without an exception.</p>
     *
     * @return The status: ACTIVE, or BUILDING after a stop of the database or an interrupt.
     * @throws IndexBuildException  If the build failed: its status is FAILED.
     */
    public JobStatus join();
    
    /**
     * As join(), but waits at most 'millis' milliseconds; 0 waits as join(). When the time
     * is up, it returns the status, BUILDING while the build goes on.
     *
     * @return The status: ACTIVE, or BUILDING after a stop, an interrupt or the time.
     * @throws IndexBuildException  If the build failed, as join().
     */
    public JobStatus join(int millis);
}
