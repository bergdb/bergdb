package bergdb.pub.util;



/**
 * Thrown when an attempt is made to use the database before it has been started
 * or when it is stopping.
 * 
 * @author Frans Lundberg
 */
public class IllegalDbStateException extends DbException {
    private static final long serialVersionUID = 1L;

    public IllegalDbStateException(String message) {
        super(message);
    }
}
