package bergdb.core;

import java.util.concurrent.atomic.AtomicLong;

/**
 * The startup stream position (startupPos) is the position in the stream the
 * the startup procedure can start from when the database is started.
 * 
 * @author Frans Lundberg
 */
public class StartupPos {
    private final AtomicLong startupPos;
    private volatile long evictPos;    // startupPos for evict
    
    public StartupPos(long startupPosParam) {
        if (startupPosParam < 0) {
            throw new IllegalArgumentException();
        }
        startupPos = new AtomicLong(startupPosParam);
        releaseForEvict();
    }
    
    /**
     * Returns the current startup stream position as a long.
     */
    public final long get() {
        return startupPos.get();
    }
    
    /**
     * Returns the last startupPos that has been released for use
     * by evict.
     */
    public final long getForEvict() {
        return evictPos;
    }
    
    /**
     * Sets the startup pos.
     * The new startup pos is not immediately available for evict. 
     * Call releaseForEvict first.
     * 
     * @param pos  A stream position, >= 0.
     */
    public void set(long pos) {
        assert pos >= 0;
        startupPos.set(pos);
    }
    
    public void releaseForEvict() {
        evictPos = startupPos.get();
    }
}
