package bergdb.pub;

/**
 * Information about the status of a stream storage.
 * 
 * @author Frans Lundberg
 */
public interface StorageInfo {
    // 1301 Frans: Yes, enums would be better, but we are not allowed to use them because of 
    // cross-compiling issues.
    
    /** The storage is initializing. */
    public static final int STATUS_INITIALIZING = 1;
    
    /** The storage is active; can be appended to and read from. */
    public static final int STATUS_ACTIVE = 2;
    
    /** The storage has an error condition. Further appends/reads will fail. */
    public static final int STATUS_ERROR = 3;

    /**
     * Returns the name of the storage. It is unique within the set of storages
     * of the database.
     */
    public String getName();
    
    /**
     * Returns the current status of the storage; one of 
     * STATUS_INITIALIZING, STATUS_ACTIVE, and STATUS_ERROR.
     */
    public int getStatus();
    
    /**
     * Returns a human-readable status string.
     */
    public String getStatusString();
    
    /**
     * Returns the confirmed length of the storage stream.
     */
    public long getConfirmedLength();
}
