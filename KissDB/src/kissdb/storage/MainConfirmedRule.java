package kissdb.storage;

import kissdb.pub.StorageInfo;

public class MainConfirmedRule implements DurabilityRule {
    
    public long computeSize(StorageInfo[] storages) {
        assert storages.length >= 1;
        StorageInfo main = storages[0];
        assert main != null;
        
        if (main.getStatus() != StorageInfo.STATUS_ACTIVE) {
            return 0;
        }
        
        return main.getConfirmedLength();
    }
}
