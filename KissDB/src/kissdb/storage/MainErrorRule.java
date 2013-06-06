package kissdb.storage;

import kissdb.pub.StorageInfo;

/**
 * This error rule says that the storage system works if the main storage is up 
 * (has status "active"). Replicas may fail and the system will continue running.
 * 
 * @author Frans Lundberg
 */
public class MainErrorRule implements ErrorRule {
    //
    // NOTE Should we have warning rule too? If main up, but replica failing, we would
    // probably want to warn about it.
    //
    public String computeError(StorageInfo[] storages) {
        assert storages.length >= 1;
        
        String result = null;
        
        StorageInfo main = storages[0];
        if (main.getStatus() != StorageInfo.STATUS_ACTIVE) {
            result = "Main storage not active. " + main.getStatusString();
        }
        
        return result;
    }
}
