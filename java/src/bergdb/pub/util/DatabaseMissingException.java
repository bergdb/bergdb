package bergdb.pub.util;

/**
 * <p>Thrown by a start when the database's directory held a database, and its stream is
 * missing (bergdb 015-01): the directory has created.txt, which a creation
 * writes once its first bytes are durable, and no stream file (*.bergdb) with a byte. The
 * stream's files were removed, or not restored or copied with created.txt, or the only one
 * was emptied. The start has opened, created and written nothing.</p>
 *
 * <p>Also thrown by a start when the directory has created.txt and its stream holds no
 * data, zeros only or a part of what a creation writes (2026-11-28, bergdb 028-88): a
 * storage that lost the only stream file's bytes and kept its length, or cut it, or another
 * file put in the place of the stream file. created.txt is written only once the creation
 * is durable, so the database was created, and it may have held data. The start has
 * written and deleted nothing; keep the files, and restore the database's files from a
 * backup, the stream files and created.txt all together. Until 028-88 such a stream gave a
 * DatabaseNotCreatedException, whose way out, the files removed, made a new database where
 * one was lost.</p>
 *
 * <p>Also thrown by a start of DatabaseBuilder.open(), which never creates a database, when
 * its directory is missing, is not a directory, or holds no stream file with a byte
 * (bergdb 015-05): a wrong path, or a volume that is not mounted. The start has
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
