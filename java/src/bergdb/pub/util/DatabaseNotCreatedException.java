package bergdb.pub.util;

/**
 * <p>Thrown by a start when the database's creation did not complete (bergdb 005-33): a
 * crash, as a power loss, while the database was created left a part of what a
 * creation writes, its first meta block and its first two records (the empty database's,
 * and the startup distance's; bergdb 028-18), and no committed transaction. The database
 * holds no data, and the start has written nothing.</p>
 *
 * <p>With the Pub API, a start that returned has made its creation durable, and the
 * exception means a crash inside that start. With the Core API (bergdb.core.Db), the
 * creation is durable only at the first sync after the start: a crash after start()
 * returned and before a sync can also give it (bergdb 028-40). A Core user that needs a
 * new database to survive a crash or a restart calls Db.sync(SyncLevel.ORDINARY) after
 * Db.start().</p>
 *
 * <p>To create the database, remove its files and start it again: in its directory, the
 * stream's files (*.bergdb) and created.txt. A stream that holds a committed transaction
 * never gives this exception.</p>
 */
public class DatabaseNotCreatedException extends DbException {
    private static final long serialVersionUID = 1L;

    /** Creates the exception with the given message. */
    public DatabaseNotCreatedException(String message) {
        super(message);
    }
}
