package bergdb.pub.util;

/**
 * <p>Thrown when the database has failed: a transaction threw after it began, because the
 * storage, the JVM or memory failed (an I/O error, a corrupt stream, an OutOfMemoryError), or
 * because of a bug; or a read or a sync failed on the storage (an I/O error, corrupt data).
 * The cause is that failure; for a call refused after it, the first one.</p>
 *
 * <p>BergDB checks everything that may refuse a transaction before the transaction changes
 * anything; such a refusal leaves the database as it was. After that point a transaction is
 * never rolled back. If it fails there, the database refuses every later transaction and
 * read with this exception until it is restarted: stop or close it, and start it again. The
 * restart rebuilds the database from its stream, as after a crash; the failed transaction is
 * then there if its record was written before the failure, and otherwise not. An in-memory
 * database is lost, as in a crash. sync() still works for the transactions before the
 * failure (bergdb 005-01).</p>
 *
 * <p>A read or a sync that fails on the storage fails the database in the same way (bergdb
 * 005-30): after an I/O error the storage below refuses all I/O, and corrupt data means lost
 * data or a bug. The call throws this exception with what it met as the cause. A read whose
 * lookup time has expired (LookupTimeNotAvailableException) does not fail the database, nor
 * does a read that runs while the database is stopping.</p>
 */
public class DbFailedException extends IllegalDbStateException {
    private static final long serialVersionUID = 1L;

    /** Creates the exception with the given message and cause. */
    public DbFailedException(String message, Throwable cause) {
        super(message);
        initCause(cause);
    }
}
