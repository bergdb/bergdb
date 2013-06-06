package kissdb.pub;

/**
 * Thrown to indicate that the supplied lookup time is too small (too long ago); the data
 * at that time is no longer available in the database.
 * 
 * @author Frans Lundberg
 */
public class LookupTimeNotAvailableException extends IllegalArgumentException {
    private static final long serialVersionUID = 1L;

    public LookupTimeNotAvailableException(String message) {
        super(message);
    }
}
