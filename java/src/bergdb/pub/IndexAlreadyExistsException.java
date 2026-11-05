package bergdb.pub;

/**
 * Thrown when an index with the specified name already exists. It belongs to the user
 * indexes, experimental in 2026.3 (see Database.indexBuilder(); bergdb 018-01, D6).
 */
public class IndexAlreadyExistsException extends RuntimeException {
    private static final long serialVersionUID = 1L;

    /** Creates the exception with the given message. */
    public IndexAlreadyExistsException(String message) {
        super(message);
    }
}
