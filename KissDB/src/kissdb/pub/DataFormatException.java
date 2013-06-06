package kissdb.pub;

/**
 * Thrown when data in the database has an illegal format.
 * 
 * @author Frans Lundberg
 */
public class DataFormatException extends DbException {
    private static final long serialVersionUID = 1L;

    public DataFormatException(String message) {
        super(message);
    }
}

/*

NOTE 1304 Frans: How does this exception relate to core.InternalDataException?
Do we need both? How used by Pub user?

*/