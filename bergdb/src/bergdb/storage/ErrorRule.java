package bergdb.storage;

import bergdb.pub.StorageInfo;

/**
 * A rule that determine whether the storage system as a whole should be 
 * considered OK or faulty.
 * 
 * @author Frans Lundberg
 */
public interface ErrorRule {
    
    /**
     * Computes the rule and returns 'null' if everything is fine, or a non-null String
     * with an error message (English, suitable for end-user).
     */
    public String computeError(StorageInfo[] storages);
}
