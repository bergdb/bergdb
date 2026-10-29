package bergdb.pub.util;

/**
 * Thrown to indicate that the supplied lookup time is too small (too long ago); the data
 * at that time is no longer available in the database.
 * 
 * @author Frans Lundberg
 */
public class LookupTimeNotAvailableException extends IllegalArgumentException {
    private static final long serialVersionUID = 1L;

    /** Creates the exception with the given message. */
    public LookupTimeNotAvailableException(String message) {
        super(message);
    }
}
