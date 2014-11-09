package bergdb.dev;

import bergdb.core.Db;
import bergdb.core.SyncLevel;
import bergdb.core.Trans;
import bergdb.dag.Keys;
import bergdb.stream.MemoryStream;

/**
 * Executable class that determins total stream size for Scenario SS2.
 * Fixed scenario without parameters. 100M of raw kv data (key+value size)
 * and 100k kvs each 1 kB. Each trans with 100 KVs.
 * Some key ordering, not random.
 * 
 * @author Frans Lundberg
 */
public class StreamSizeSS2 {
    int kvsPerTrans = 100;
    int n = 100*1000 / kvsPerTrans;
    int keySize = 10;
    int valueSize = 1000 - keySize;
    Db db;
    
    private void go() {
        createDb();
        addTransactions();
        reportResult();
    }

    private void createDb() {
        MemoryStream stream = new MemoryStream();
        db = Db.builder().mainStream(stream).start();
    }
    
    private void addTransactions() {
        int counter = 0;
        
        for (int i = 0; i < n; i++) {
            Trans.Builder b = Trans.builder();
            
            for (int j = 0; j < kvsPerTrans; j++) {
                long[] key = Keys.toSegments("k-" + counter);
                b.put(key, new byte[valueSize]);
                counter++;
            }
            
            db.execute(b.build());
        }
        
        db.sync(SyncLevel.ORDINARY);
    }

    private void reportResult() {
        long length = db.getStreamLength();
        long dataSize = n * kvsPerTrans * (keySize + valueSize);
        double factor = ((double) length) / dataSize;
        
        System.out.printf("dataSize: %.1fM\n", (1e-6 * dataSize));
        System.out.printf("streamLength: %.1fM\n", (1e-6 * length));
        System.out.printf("factor: %.2f\n", factor);
    }

    public static void main(String[] args) {
        new StreamSizeSS2().go();
    }
}
