package bergdb.storage;

import bergdb.pub.util.DbException;

/**
 * Thrown when there is an error in the underlying stream of
 * the database.
 * Subclasses: StreamFormatException (among its subclasses BadMagicBytes and
 * VersioningStreamException), StreamIoException.
 * 
 * @author Frans Lundberg
 */
public abstract class StreamException extends DbException {
    private static final long serialVersionUID = 1L;

    public StreamException(String message) {
        super(message);
    }
    
    public StreamException(String message, Throwable cause) {
        super(message, cause);
    }
}
