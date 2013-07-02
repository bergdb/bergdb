package bergdb.pub;

/**
 * Thrown to indicate that the replica state is illegal.
 * 
 * @author Frans Lundberg
 */
public class BadReplicaException extends RuntimeException {
    private static final long serialVersionUID = 1L;

    public BadReplicaException(String message) {
        super(message);
    }
}
