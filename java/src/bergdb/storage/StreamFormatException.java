package bergdb.storage;


/**
 * This exception is thrown to indicate that the bytes in the stream 
 * does not follow the agreed on format.
 * 
 * @author Frans Lundberg
 */
public class StreamFormatException extends StreamException {
    private static final long serialVersionUID = 1L;

    public StreamFormatException(String message) {
        super(message);
    }
    
    public StreamFormatException(String message, Throwable cause) {
        super(message, cause);
    }
}
