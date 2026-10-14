package bergdb.pub;

/**
 * Thrown to indicate that no object with the specified name or key exists.
 */
public class NoSuchObjectException extends RuntimeException {
    private static final long serialVersionUID = 1L;
    
    public NoSuchObjectException(String message) {
        super(message);
    }
}
