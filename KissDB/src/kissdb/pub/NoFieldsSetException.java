package kissdb.pub;

/**
 * Thrown if no object field was set.
 */
public class NoFieldsSetException extends RuntimeException {
    private static final long serialVersionUID = 1L;

    public NoFieldsSetException(String message) {
        super(message);
    }
}
