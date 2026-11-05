package bergdb.pub;

/**
 * Thrown to indicate that there is no field in the object that can be used as a database key.
 * It belongs to put(Object), experimental in 2026.3 (see WBuilder.put(Object); bergdb
 * 018-01, D6).
 * 
 * @author Frans Lundberg
 */
public class MissingKeyFieldException extends RuntimeException {
    private static final long serialVersionUID = 1L;

    /** Creates the exception with the given message. */
    public MissingKeyFieldException(String message) {
        super(message);
    }
}
