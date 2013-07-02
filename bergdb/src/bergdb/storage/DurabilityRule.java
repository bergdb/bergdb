package bergdb.storage;

import bergdb.pub.StorageInfo;

/**
 * A durability rule computes the durable stream size based on data from the main storage 
 * and replicas.
 * 
 * @author Frans Lundberg
 */
public interface DurabilityRule {
    // Should we have ability to return error string in case 0 is returned?
    // Should we have separate error rule?
    
    /**
     * Computes the durable size.
     * 
     * @return The durable size or -1 if the durability requested cannot be attained because
     * one or more storages have failed (are not active). A 0-value return indicates that the
     * whole storage as a unit should be considered faulty.
     */
    long computeSize(StorageInfo[] storages);
}
