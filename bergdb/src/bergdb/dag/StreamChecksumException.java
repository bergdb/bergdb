package bergdb.dag;

import bergdb.storage.StreamFormatException;

/**
 * Thrown if a an data integrity checksum in the database stream is bad.
 * 
 * @author Frans Lundberg
 */
public class StreamChecksumException extends StreamFormatException {
    private static final long serialVersionUID = 1L;

    public StreamChecksumException(String message) {
        super(message);
    }
}
