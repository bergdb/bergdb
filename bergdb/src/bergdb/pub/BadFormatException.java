package bergdb.pub;

/**
 * Thrown when the format (syntax) of data is not according to specification.
 * 
 * @author Frans Lundberg
 */
public class BadFormatException extends RuntimeException {
    private static final long serialVersionUID = 1L;

    public BadFormatException(String message) {
        super(message);
    }
}
