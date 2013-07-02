package bergdb.core;

import bergdb.pub.IllegalDbStateException;

/**
 * Thrown when an attempt is made to use the database when it is stopping.
 * 
 * @author Frans Lundberg
 */
public class DbStoppingException extends IllegalDbStateException {
    private static final long serialVersionUID = 1L;

    public DbStoppingException(String message) {
        super(message);
    }
}
