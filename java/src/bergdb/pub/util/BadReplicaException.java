package bergdb.pub.util;

/**
 * Thrown to indicate that the replica state is illegal. Replication is experimental (see
 * Database.addReplica()).
 * 
 * @author Frans Lundberg
 */
public class BadReplicaException extends RuntimeException {
    private static final long serialVersionUID = 1L;

    /** Creates the exception with the given message. */
    public BadReplicaException(String message) {
        super(message);
    }
}
