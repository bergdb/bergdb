package bergdb.pub.util;

/**
 * The sync level of Database.sync(SyncLevel) and Connection.sync(SyncLevel): the durability
 * rule that the sync waits for.
 * 
 * <p>There is no level for a copy elsewhere, such as a replica; one may come with a future
 * replication design, as a level or as a call of its own (bergdb 005-11, 017-03).</p>
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
