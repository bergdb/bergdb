package bergdb.pub.util;

/**
 * The status of an index's build at one moment (bergdb 020-10, section 3.2): immutable.
 *
 * @see Job
 * @author Frans Lundberg
 */
public interface JobStatus {
    
    /** The state of a build. */
    public enum State {
        /** The build runs, or waits for the next start of the database. */
        BUILDING,
        /** The index is active: built, and kept by every write. */
        ACTIVE,
        /**
         * The build failed, and Job.join() throws IndexBuildException: the index was deleted
         * while it was building (the reason "deleted"), or the build met an exception that is
         * neither a stop of the database nor a refusal, such as data that it cannot index
         * (DataFormatException) or a bug. The database goes on. A deleted index is gone; for
         * any other, the failure is kept in this process only: the next start takes the build
         * again.
         */
        FAILED
    }
    
    /** The state. */
    public State state();
    
    /**
     * The values of the directory the build has read, in this process: its progress, without
     * a total (IndexBuilder.start(); bergdb 020-24-04, U4-3).
     */
    public long count();
    
    /** If FAILED: why, in English, with the cause's class and message; else null. */
    public String reason();
    
    /** One line in English made from the state, the count and the reason. */
    public String note();
}
