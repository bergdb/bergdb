package bergdb.dev;

import bergdb.core.Db;
import bergdb.core.SyncLevel;
import bergdb.core.Trans;
import bergdb.dag.Keys;
import bergdb.stream.MemoryStream;

/**
 * Executable class that determins total stream size for Scenario SS1.
 * Fixed scenario without parameters. 100M of raw kv data (key+value size)
 * and 100k kvs each 1 kB. Each trans with one single kv.
 * Some key ordering, not random.
 * 
 * @author Frans Lundberg
 */
public class StreamSizeSS1 {
    int n = 100*1000;
    int keySize = 10;
    int valueSize = 1000 - keySize;
    Db db;
    
    private void go() {
        createDb();
        addSingleKvTransactions();
        reportResult();
    }

    private void createDb() {
        MemoryStream stream = new MemoryStream();
        db = Db.builder().mainStream(stream).start();
    }
    
    private void addSingleKvTransactions() {        
        for (int i = 0; i < n; i++) {
            long[] key = Keys.toSegments("k-" + i);
            Trans t = Trans.builder().put(key, new byte[valueSize]).build();
            db.execute(t);
        }
        
        db.sync(SyncLevel.ORDINARY);
    }

    private void reportResult() {
        long length = db.getStreamLength();
        long dataSize = n * (keySize + valueSize);
        double factor = ((double) length) / dataSize;
        
        System.out.printf("dataSize: %.1fM\n", (1e-6 * dataSize));
        System.out.printf("streamLength: %.1fM\n", (1e-6 * length));
        System.out.printf("factor: %.2f\n", factor);
    }

    public static void main(String[] args) {
        new StreamSizeSS1().go();
    }
}
