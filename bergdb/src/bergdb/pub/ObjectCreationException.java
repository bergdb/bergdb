package bergdb.pub;

/**
 * Thrown when an object should have been created, but could not be created.
 * 
 * @author Frans Lundberg
 */
public class ObjectCreationException extends RuntimeException {
    private static final long serialVersionUID = 1L;

    public ObjectCreationException(String message) {
        super(message);
    }
}
