package bergdb.pub.util;

/**
 * <p>Thrown when the database has failed: a transaction threw after it began, because the
 * storage, the JVM or memory failed (an I/O error, a corrupt stream, an OutOfMemoryError), or
 * because of a bug. The cause is that first failure.</p>
 *
 * <p>BergDB checks everything that may refuse a transaction before the transaction changes
 * anything; such a refusal leaves the database as it was. After that point a transaction is
 * never rolled back. If it fails there, the database refuses every later transaction and
 * read with this exception until it is restarted: stop or close it, and start it again. The
 * restart rebuilds the database from its stream, as after a crash; the failed transaction is
 * then there if its record was written before the failure, and otherwise not. An in-memory
 * database is lost, as in a crash. sync() still works for the transactions before the
 * failure (bergdb 005-01).</p>
 */
public class DbFailedException extends IllegalDbStateException {
    private static final long serialVersionUID = 1L;

    public DbFailedException(String message, Throwable cause) {
        super(message);
        initCause(cause);
    }
}
