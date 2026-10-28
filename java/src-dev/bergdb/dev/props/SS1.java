package bergdb.dev.props;

import bergdb.core.Db;
import bergdb.core.Trans;
import bergdb.dag.Keys;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.MemoryStream;

/**
 * Executable class that determines total stream size for Scenario SS1.
 * Fixed scenario without parameters. 100M of raw kv data (key+value size)
 * and 100k kvs each 1 kB. Each trans with 100 KVs.
 * Some key ordering, not random.
 * 
 * @author Frans Lundberg
 */
public class SS1 {
    int keySize = 10;
    int valueSize = 1000 - keySize;
    int kvsPerTrans = 100;
    int transCount = 100*1000 / kvsPerTrans;
    Db db;
    
    double factor;
    long dataSize;
    long length;
    
    /**
     * Runs the stream size test and returns the result.
     */
    public double go() {
        createDb();
        runTransactions();
        return computeResult();
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
    
    private double computeResult() {
        length = db.getStreamLength();
        dataSize = transCount * kvsPerTrans * (keySize + valueSize);
        factor = ((double) length) / dataSize;
        return factor;
    }

    void reportResult() {
        System.out.printf("Factor: %.2f\n", factor);
        System.out.printf("(dataSize: %.1fM, kv size: %d, stream length: %.1fM, kvsPerTrans:%d)\n", 
                1e-6 * dataSize, keySize + valueSize, 1e-6 * length, kvsPerTrans);
    }

    public static void main(String[] args) {
        SS1 ss1 = new SS1();
        ss1.go();
        ss1.reportResult();
    }
}

/*
150105 Frans: got Factor 1.25.

*/
