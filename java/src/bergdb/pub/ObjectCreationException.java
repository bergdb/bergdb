package bergdb.pub;

/**
 * Thrown when an object should have been created, but could not be created. It belongs to
 * a value that is neither a String nor a byte[], experimental in 2026.3 (see
 * Connection.get(); bergdb 018-01, D6).
 * 
 * @author Frans Lundberg
 */
public class ObjectCreationException extends RuntimeException {
    private static final long serialVersionUID = 1L;

    /** Creates the exception with the given message. */
    public ObjectCreationException(String message) {
        super(message);
    }
}
