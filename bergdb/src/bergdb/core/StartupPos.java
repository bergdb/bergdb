package bergdb.core;

import java.util.concurrent.atomic.AtomicLong;

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
    private final AtomicLong pos2;
    private volatile long evictPos;    // startupPos for evict
    
    public StartupPos(long startupPos) {
        if (startupPos < 0) {
            throw new IllegalArgumentException();
        }
        pos2 = new AtomicLong(startupPos);
        releaseForEvict();
    }
    
    /**
     * Returns the current startup stream position as a long.
     */
    public final long get() {
        return pos2.get();
    }
    
    /**
     * Returns the last startupPos that has been released for use
     * by evict.
     */
    public final long getForEvict() {
        return this.evictPos;
    }
    
    /**
     * Sets the startup pos.
     * The new startup pos is not immediately available for evict. 
     * Call releaseForEvict first.
     * 
     * @param pos  A stream position, >= 0.
     */
    public void set(long pos) {
        if (pos < 0) throw new IllegalArgumentException("Bad stream pos: " + pos);
        this.pos2.set(pos);
    }
    
    /**
     * Computes a new current startup pos based on the current one, 
     * the startup distance and the current transaction size.
     * SYNC note: method protected by Db.writeLock.
     * The new startup pos is not immediately available to getEvictPos().
     * 
     * @param startupDistance  The current startupDistance of the database.
     * @param streamLength  The current stream length before the current transaction
     * is appended to the stream.
     * @return  The next (now current) startup position.
     */
    public long next(long startupDistance, long streamLength) {
        // TODO D. Consider: include size of current transaction in calculation.
        
        long current = pos2.get();
        long candidate = streamLength - startupDistance;
        candidate = candidate < 0 ? 0 : candidate;
        candidate = candidate < current ? current : candidate;
        
        boolean updated = pos2.compareAndSet(current, candidate);
        if (!updated) {
            throw new Error("Should not happend, pos was updated by other thread.");
        }
        
        return pos2.get();
    }
    
    public void releaseForEvict() {
        evictPos = pos2.get();
    }
}
