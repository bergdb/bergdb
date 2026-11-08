package bergdb.pub;

/**
 * Thrown when an object should have been created, but could not be created: the class is
 * not a Data Object class, its constructor threw, or the value is not a stored object (bergdb
 * 020-09, section 5.2). It belongs to a value that is neither a String nor a byte[] (see
 * Connection.get()).
 * 
 * @author Frans Lundberg
 */
public class ObjectCreationException extends RuntimeException {
    private static final long serialVersionUID = 1L;

    /** Creates the exception with the given message. */
    public ObjectCreationException(String message) {
        super(message);
    }

    /** Creates the exception with the given message and cause, such as a constructor's. */
    public ObjectCreationException(String message, Throwable cause) {
        super(message, cause);
    }
}
