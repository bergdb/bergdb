package bergdb.pub.util;

/**
 * <p>Thrown by a start when the database's directory held a database, and its stream is
 * missing (2026-11-03, bergdb 015-01): the directory has created.txt, which a creation
 * writes once its first bytes are durable, and no stream file (*.bergdb) with a byte. The
 * stream's files were removed, or not restored or copied with created.txt, or the only one
 * was emptied. The start has opened, created and written nothing. Before, such a start
 * created a new, empty database there, and said nothing.</p>
 *
 * <p>Also thrown by a start of DatabaseBuilder.open(), which never creates a database, when
 * its directory is missing, is not a directory, or holds no stream file with a byte
 * (2026-11-05, bergdb 015-05): a wrong path, or a volume that is not mounted. The start has
 * then created and written nothing; DatabaseBuilder.create() creates a database there.</p>
 *
 * <p>To start the database, restore its stream's files (*.bergdb) from a backup, into the
 * directory, and start again. To create a new, empty database there instead, remove
 * created.txt and the empty *.bergdb files, and start again.</p>
 */
public class DatabaseMissingException extends DbException {
    private static final long serialVersionUID = 1L;

    /** Creates the exception with the given message. */
    public DatabaseMissingException(String message) {
        super(message);
    }
}
