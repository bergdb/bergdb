package bergdb.pub.util;

/**
 * <p>Thrown by Job.join() and join(int) when the build of an index failed (bergdb 020-10,
 * section 3.2), each time they are called, as Future.get() throws for a task that failed.
 * getStatus() gives the job's last status, FAILED, and getCause() the exception that
 * failed the build; Job.getStatus() gives the same status without a throw.</p>
 *
 * <p>A build fails when:</p>
 * <ul>
 * <li>the index was deleted while it was building: the reason is "deleted", and there is
 *     no cause;</li>
 * <li>it met data that it cannot index, such as an object of the format of BergDB 2026.3 and
 *     before: the cause is a DataFormatException, or an InternalDataException for corrupt
 *     internal data (see IndexBuilder);</li>
 * <li>it met any other RuntimeException, a bug in BergDB: that exception is the cause.</li>
 * </ul>
 *
 * <p>The database goes on. A deleted index is gone. Any other index whose build failed stays,
 * building: the failure is kept in this process only, and the next start takes the build
 * again from the first key of its directory. Delete the index (Database.deleteIndex()), or
 * replace or delete the values that the build cannot index and restart. A stop of the
 * database during the build is no failure: join() then returns the status BUILDING.</p>
 *
 * <p>Not a DbException: a DbException is a refusal of a request, which may be made again, or
 * a failure of the database, and this is neither.</p>
 *
 * @author Frans Lundberg
 */
public class IndexBuildException extends RuntimeException {
    private static final long serialVersionUID = 1L;

    private final JobStatus status;

    /**
     * Creates the exception for the failed build of the index 'indexName': its message names
     * the index and the status's reason.
     *
     * @param indexName  The index's name.
     * @param status  The job's last status, FAILED.
     * @param cause  The exception that failed the build, or null if there is none.
     */
    public IndexBuildException(String indexName, JobStatus status, Throwable cause) {
        super("The build of the index " + indexName + " failed: " + status.reason(), cause);
        this.status = status;
    }

    /** The job's status when the build failed: immutable, its state FAILED. */
    public JobStatus getStatus() {
        return status;
    }
}
