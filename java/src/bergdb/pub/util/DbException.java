package bergdb.pub.util;

/**
 * <p>Thrown when the database cannot do what was asked. There are two kinds.</p>
 * 
 * <p>A refusal: the database checked the request and refused it before it changed
 * anything, for example a transaction that is too large (its values, or the index nodes
 * it can make dirty: bergdb 005-17, 005-31), a clock time out of range, or
 * a stored value that does not fit its Java field (DataFormatException). The database
 * is as it was and can be used on. Each such case says so where it is thrown.</p>
 * 
 * <p>A failure: the storage, the JVM or memory failed, or there is a bug. A failure in
 * a transaction fails the database: every later transaction and read throws a
 * DbFailedException until the database is restarted. So does a stream error in a read
 * or a sync, an I/O error or corrupt data (bergdb 005-30): the call throws a
 * DbFailedException with the StreamIoException or the StreamFormatException as the
 * cause. Corrupt internal data (InternalDataException) means that the stream does not
 * work either; restart the database.</p>
 * 
 * <p>An application that does not tell the two apart can take any DbException as a
 * reason to stop and restart the database; that is always safe (2026-10-23, bergdb
 * 005-01; before, this comment called every DbException fatal).</p>
 * 
 * @author Frans Lundberg
 */
public class DbException extends RuntimeException {
    private static final long serialVersionUID = 1L;
    
    /** Creates the exception with the given message. */
    public DbException(String message) {
        super(message);
    }
    
    /** Creates the exception with the given message and cause. */
    public DbException(String message, Throwable cause) {
        super(message, cause);
    }
}

/*
The Pub user typically do not need to catch different database exceptions:
StreamFormatException / StreamException / InternalDataException in different 
catch-clauses. It is enough to catch DBException.
The subclasses of DBException do not have to be a part of Pub layer, but they
can still be thrown by Core Layer and handled (as a DbException) by Pub layer.
*/