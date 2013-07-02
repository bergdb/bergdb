package bergdb.storage;


/**
 * A StreamException is thrown to indicate that the read data does not follow
 * the DB stream format.
 * It is not thrown to indicate a problem reading from the stream or writing
 * to it.
 */
public class StreamFormatException extends StreamException {
    private static final long serialVersionUID = 1L;

    public StreamFormatException(String message) {
        super(message);
    }
}
