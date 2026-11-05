package bergdb.pub;

/**
 * Thrown to indicate that no index with the given name exists. It belongs to the user
 * indexes, experimental in 2026.3 (see Database.indexBuilder(); bergdb 018-01, D6).
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
