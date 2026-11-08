package bergdb.pub;

import bergdb.pub.util.DbException;

/**
 * Thrown when data in the database has an illegal format: a stored object that cannot be
 * read when its index entries are updated or built; a value read as a String that is not
 * well-formed UTF-8 (bergdb 021-06). A get never throws it for a value that does not fit
 * the field it is read into: it converts best effort (bergdb 020-09, section 5). It belongs
 * to the objects and the user indexes (see Connection.get(), WBuilder.put(String, Object)
 * and Database.indexBuilder()), and to String values.
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