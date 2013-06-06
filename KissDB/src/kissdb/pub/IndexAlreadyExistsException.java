package kissdb.pub;

/**
 * Thrown when an index with the specified name already exists.
 */
public class IndexAlreadyExistsException extends RuntimeException {
    private static final long serialVersionUID = 1L;

    public IndexAlreadyExistsException(String message) {
        super(message);
    }
}
