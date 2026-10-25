package bergdb.core;

/**
 * The sync level for method Database.sync() and others determine
 * what durability rule to apply to do the sync.
 * 
 * @author Frans Lundberg
 */
public enum SyncLevel {
    
    /** No sync; do nothing. */ 
    NONE(10),
    
    /** Sync to ordinary durability. */
    ORDINARY(20),
    
    /** 
     * Sync to strong durability: the main storage and a replica. Replication is
     * experimental (2026-10-25, bergdb 005-11): when no replica is active (none, or only
     * failed ones), it is ORDINARY, and with several, the fastest one meets it.
     */
    STRONG(30);
    
    private final int value;
    
    private SyncLevel(int value) {
        this.value = value;
    }
}
