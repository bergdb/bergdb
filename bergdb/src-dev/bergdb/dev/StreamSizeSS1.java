package bergdb.dev;

import bergdb.core.Db;
import bergdb.core.SyncLevel;
import bergdb.core.Trans;
import bergdb.dag.Keys;
import bergdb.stream.MemoryStream;

/**
 * Executable class that determines total stream size for Scenario SS1.
 * Fixed scenario without parameters. 100M of raw kv data (key+value size)
 * and 100k kvs each 1 kB. Each trans with one single kv.
 * Some key ordering, not random.
 * 
 * @author Frans Lundberg
 */
public class StreamSizeSS1 {
    int transCount = 100*1000;
    int keySize = 10;
    int valueSize = 1000 - keySize;
    int kvsPerTrans = 1;
    Db db;
    
    public void go() {
        createDb();
        runTransactions();
        reportResult();
    }

    private void createDb() {
        MemoryStream stream = new MemoryStream();
        db = Db.builder().mainStream(stream).start();
    }
    
    private void runTransactions() {
        int counter = 0;
        
        for (int i = 0; i < transCount; i++) {
            Trans.Builder b = db.trans();
            
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
        long dataSize = transCount * kvsPerTrans * (keySize + valueSize);
        double factor = ((double) length) / dataSize;
        
        System.out.printf("Factor: %.2f\n", factor);
        System.out.printf("(dataSize: %.1fM, kv size: %d, stream length: %.1fM)\n", 
                1e-6 * dataSize, keySize + valueSize, 1e-6 * length);
    }

    public static void main(String[] args) {
        new StreamSizeSS1().go();
    }
}

/*

150103 Frans: Result. Factor: 1.21.

Result for SS1/2/3, 150103: 1.21, 1.15, 2.02.

*/
