package kissdb.storage;

import kissdb.pub.DbException;

/**
 * Thrown when there is an error in the underlying stream of
 * the database.
 */
public abstract class StreamException extends DbException {
    private static final long serialVersionUID = 1L;

    public StreamException(String message) {
        super(message);
    }
}
