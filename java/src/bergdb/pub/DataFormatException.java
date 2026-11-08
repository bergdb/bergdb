package bergdb.pub;

import bergdb.pub.util.DbException;

/**
 * Thrown when data in the database has an illegal format: a stored value that does not fit
 * the Java type or field it is read into, or a stored object that cannot be read when its
 * index entries are updated or built. It belongs to the object code and the user indexes,
 * experimental in 2026.3 (see Connection.get(), WBuilder.put(String, Object) and
 * Database.indexBuilder(); bergdb 018-01, D6).
 * 
 * @author Frans Lundberg
 */
public class DataFormatException extends DbException {
    private static final long serialVersionUID = 1L;

    /** Creates the exception with the given message. */
    public DataFormatException(String message) {
        super(message);
    }
}

/*

NOTE 1304 Frans: How does this exception relate to core.InternalDataException?
Do we need both? How used by Pub user?

*/