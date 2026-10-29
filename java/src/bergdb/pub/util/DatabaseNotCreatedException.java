package bergdb.pub.util;

/**
 * <p>Thrown by a start when the database's creation did not complete (2026-10-25, bergdb
 * 005-33): a crash, as a power loss, while the database was created left a part of what a
 * creation writes, its first meta block and its first transaction, and no committed
 * transaction. The database holds no data, and the start has written nothing.</p>
 *
 * <p>To create the database, remove its files and start it again: in its directory, the
 * stream's files (*.bergdb) and created.txt, and the replicas' files. A stream that holds
 * a committed transaction never gives this exception. Before, such a database failed every
 * start with a StreamFormatException that did not say what had happened, or what to do.</p>
 */
public class DatabaseNotCreatedException extends DbException {
    private static final long serialVersionUID = 1L;

    /** Creates the exception with the given message. */
    public DatabaseNotCreatedException(String message) {
        super(message);
    }
}
