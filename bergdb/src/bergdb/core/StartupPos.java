package bergdb.core;

// TODO A. Consider letting this class handle startupDistance too.

/**
 * The startup stream position (startupPos) is the position in the stream the
 * the startup procedure can start from when the database is started.
 * An object of this class handles the startupPos by updating it based on 
 * the startupDistance, the size of the current transaction and the 
 * current stream length.
 * 
 * @author Frans Lundberg
 */
public class StartupPos {
    private long pos;
    
    public StartupPos(long startupPos) {
        if (startupPos < 0) {
            throw new IllegalArgumentException();
        }
        pos = startupPos;
    }
    
    /**
     * Returns the current startup stream position as a long.
     */
    public final long get() {
        return pos;
    }
    
    /**
     * Sets the startup pos.
     * 
     * @param pos  A stream position, >= 0.
     */
    public void set(long pos) {
        if (pos < 0) throw new IllegalArgumentException("Bad stream pos: " + pos);
        this.pos = pos;
    }
    
    /**
     * Computes a new current startup pos based on the current one, 
     * the startup distance and the current transaction size.
     * 
     * @param startupDistance  The current startupDistance of the database.
     * @param streamLength  The current stream length before the current transaction
     * is appended to the stream.
     * @return  The next (now current) startup position.
     */
    public long next(long startupDistance, long streamLength) {
        // TODO E. Improve by including size of current transaction.
        long current = pos;
        long candidate = streamLength - startupDistance;
        candidate = candidate < 0 ? 0 : candidate;
        candidate = candidate < current ? current : candidate;
        this.pos = candidate;
        return this.pos;
    }
}
