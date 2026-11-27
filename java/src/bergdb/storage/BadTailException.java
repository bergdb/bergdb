package bergdb.storage;

/**
 * Thrown by a start's recovery for a tail of the stream that is not the stream's own records
 * (bergdb 028-67, C1): from a position P, the end of the last record found to be one, the
 * stream holds bytes that are not a record of this database at their place, such as zeros
 * past a record's end, or another file's bytes that a kill of the process during an append
 * can leave within the last stream file's length (macOS, APFS; bergdb 035-02). Thrown before
 * the recovery writes anything; its message names the cause and the way out, a cut of the
 * stream at P (getCutPos()).
 *
 * @author Frans Lundberg
 */
public class BadTailException extends StreamFormatException {
    private static final long serialVersionUID = 1L;

    private final long cutPos;

    public BadTailException(String message, long cutPos) {
        super(message);
        this.cutPos = cutPos;
    }

    /** P, the stream position to cut the stream at: the end of the last record that is one. */
    public long getCutPos() {
        return cutPos;
    }
}
