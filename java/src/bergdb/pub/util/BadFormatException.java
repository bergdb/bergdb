package bergdb.pub.util;

/**
 * Thrown when the format (syntax) of data is not according to specification.
 * 
 * @author Frans Lundberg
 */
public class BadFormatException extends RuntimeException {
    private static final long serialVersionUID = 1L;

    /** Creates the exception with the given message. */
    public BadFormatException(String message) {
        super(message);
    }
}
