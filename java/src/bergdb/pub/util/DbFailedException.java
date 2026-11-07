package bergdb.pub.util;

/**
 * <p>Thrown when the database has failed, as Database's Javadoc says ("Errors"): its
 * environment failed (an I/O error or corrupt data in the storage, an Error such as an
 * OutOfMemoryError) or a bug, in a read, a transaction or a sync, or a transaction failed
 * after its checks. The cause is that failure; for a call refused after it, the first one. The
 * call that met an Error throws the Error itself, and the later calls this exception with
 * the Error as the cause (bergdb 019-10).</p>
 *
 * <p>BergDB checks everything that may refuse a transaction before the transaction changes
 * anything; such a refusal leaves the database as it was. After that point a transaction is
 * never rolled back. After a failure, the database refuses every later transaction and read
 * with this exception; the application should end its process, and the next start rebuilds
 * the database from its stream, as after a crash: the failed transaction is then there if
 * its record was written before the failure, and otherwise not. An in-memory database is
 * lost, as in a crash. sync() still works for the transactions before the failure while the
 * storage does, and so do stop() and close() (bergdb 005-01, 005-30).</p>
 *
 * <p>A read whose lookup time has expired (LookupTimeNotAvailableException) does not fail
 * the database, nor does a read that runs while the database is stopping.</p>
 */
public class DbFailedException extends IllegalDbStateException {
    private static final long serialVersionUID = 1L;

    /** Creates the exception with the given message and cause. */
    public DbFailedException(String message, Throwable cause) {
        super(message);
        initCause(cause);
    }
}
