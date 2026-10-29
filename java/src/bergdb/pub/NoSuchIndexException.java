package bergdb.pub;

/**
 * Thrown to indicate that no index with the given name exists.
 * 
 * @author Frans Lundberg
 */
public class NoSuchIndexException extends RuntimeException {
    private static final long serialVersionUID = 1L;
    
    /** Creates the exception with the given message. */
    public NoSuchIndexException(String message) {
        super (message);
    }
}
