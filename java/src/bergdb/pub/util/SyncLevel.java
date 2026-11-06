package bergdb.pub.util;

/**
 * The sync level of Database.sync(SyncLevel) and Connection.sync(SyncLevel): the durability
 * rule that the sync waits for.
 * 
 * <p>Until 2026-11-04 there was a third level, STRONG (30): the main storage and a
 * replica. It went with replication (bergdb 005-11, options A and C2); a wait for a copy
 * elsewhere may come back with a future replication design, as a level or as a call of its
 * own (bergdb 017-03).</p>
 * 
 * @author Frans Lundberg
 */
public enum SyncLevel {
    
    /** No sync; do nothing. */ 
    NONE(10),
    
    /**
     * Sync to ordinary durability: the bytes are on the main storage, with a file storage
     * forced to the device.
     */
    ORDINARY(20);
    
    private final int value;
    
    private SyncLevel(int value) {
        this.value = value;
    }
}
