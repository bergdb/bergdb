package bergdb.storage;

import java.io.IOException;

/**
 * Thrown when it was not possible to read from or write to the underlying storage.
 * 
 * @author Frans Lundberg
 */
public class StreamIoException extends StreamException {
    private static final long serialVersionUID = 1L;

    /**
     * This constructor sets the "cause" of the exception properly.
     */
    public StreamIoException(String message, IOException cause) {
        super(message);
        this.initCause(cause);
    }
    
    /**
     * Uses the message of the provided exception.
     * This constructor sets the "cause" of the exception properly.
     */
    public StreamIoException(IOException e) {
        super(e.getMessage());
        this.initCause(e);
    }
}
