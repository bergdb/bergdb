package bergdb.pub;

/**
 * Thrown when there is no index of the given name: by Database.deleteIndex() and
 * Database.indexJob() now, and by Connection.useIndex() at the lookup time, also when the
 * index is building then (bergdb 020-10, sections 3.2 and 3.6).
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
