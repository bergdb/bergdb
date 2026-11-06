package bergdb.pub.util;

/**
 * Thrown when an attempt is made to use the database before it has been started,
 * when it is stopping or stopped, or after it has failed (DbFailedException).
 * 
 * @author Frans Lundberg
 */
public class IllegalDbStateException extends DbException {
    private static final long serialVersionUID = 1L;

    /** Creates the exception with the given message. */
    public IllegalDbStateException(String message) {
        super(message);
    }
}
