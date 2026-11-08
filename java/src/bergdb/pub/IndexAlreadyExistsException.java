package bergdb.pub;

/**
 * Thrown by IndexBuilder.start() when an index of the name exists, building or active
 * (bergdb 020-10, section 3.1).
 */
public class IndexAlreadyExistsException extends RuntimeException {
    private static final long serialVersionUID = 1L;

    /** Creates the exception with the given message. */
    public IndexAlreadyExistsException(String message) {
        super(message);
    }
}
