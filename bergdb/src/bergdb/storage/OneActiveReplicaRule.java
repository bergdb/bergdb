package bergdb.storage;

import bergdb.pub.util.StorageInfo;

/**
 * With this rule, data is considered durable when it has been written to the main storage 
 * plus to at least one replica, if active replicas exists. If no active replica exist, this
 * rule only requires that data has been written to the main storage.
 * 
 * @author Frans Lundberg
 */
public class OneActiveReplicaRule implements DurabilityRule {
    
    public long computeSize(StorageInfo[] storages) {
        assert storages.length >= 1;
        
        StorageInfo main = storages[0];
        long mainSize = main.getConfirmedLength();
        long maxConfirmedByReplica = 0;
        int activeCount = 0;
        
        if (main.getStatus() != StorageInfo.STATUS_ACTIVE) {
            return 0;
        }
        
        for (int i = 1; i < storages.length; i++) {
            StorageInfo r = storages[i];
            if (r.getStatus() == StorageInfo.STATUS_ACTIVE) {
                activeCount++;
                long confirmed = r.getConfirmedLength();
                
                if (confirmed > maxConfirmedByReplica) {
                    maxConfirmedByReplica = confirmed;
                    if (maxConfirmedByReplica >= mainSize) {
                        break;
                    }
                }
            }
        }
        
        long result;
        if (activeCount == 0) {
            result = mainSize;
        } else {
            result = Math.min(mainSize, maxConfirmedByReplica);
        }

//System.out.println("OneActiveReplica, result = " + result);
        
        return result;
    }
}
