package bergdb.pub.util;

/**
 * Thrown when a read needs data that reclaim has removed: its lookup time is before the
 * first available lookup time, or became so while it ran (a cut overtook it); or, by
 * Connection.transactionInfo(), the transaction that wrote the value read is before that
 * time and no longer available (bergdb 021-17). The read is refused, and the database goes
 * on.
 * 
 * @author Frans Lundberg
 */
public class LookupTimeNotAvailableException extends IllegalArgumentException {
    private static final long serialVersionUID = 1L;

    /** Creates the exception with the given message. */
    public LookupTimeNotAvailableException(String message) {
        super(message);
    }
}
