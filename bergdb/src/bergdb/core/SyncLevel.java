package bergdb.core;

// XXX
// TODO A. Document sync levels here.
// TODO A. Change Connection, Database, Transaction APIs. sync(SyncLevel) instead of syncStrong().
// TODO A. Make syncStrong() deprecated.

/**
 * Sync level for Database.sync() method.
 * 
 * @author Frans Lundberg
 */
public enum SyncLevel {
    
    /** No sync; do nothing. */ 
    NONE(10),
    
    /** Sync to ordinary durability. */
    ORDINARY(20),
    
    /** Sync to strong durability. */
    STRONG(30);
    
    private int value;
    
    SyncLevel(int value) {
        this.value = value;
    }
}
