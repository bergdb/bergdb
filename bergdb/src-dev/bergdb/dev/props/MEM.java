package bergdb.dev.props;
import bergdb.core.Db;
import bergdb.core.Trans;
import bergdb.stream.DummyStream;

/**
 * Computes the MEM property; the memory usage per KV in a database
 * with one million small KVs.
 * 
 * @author Frans Lundberg.
 */
public class MEM {
    String report;

    public double go() {
        int n = 1000*1000;
        int valueSize = 0;
        Runtime rt = Runtime.getRuntime();
        Db db = Db.builder().testSetup().mainStream(new DummyStream()).start();
        
        System.gc(); System.gc(); System.gc();
        long emptyMem = rt.totalMemory() - rt.freeMemory();
        
        int batchSize = 100;
        for (int i = 0; i < n/batchSize; i++) {
            Trans.Builder b = db.trans();
            for (int j = 0; j < batchSize; j++) {
                String key = "" + (i*batchSize + j);
                byte[] value = new byte[valueSize];
                b.put(key, value);
            }
            Trans t = b.build();
            db.execute(t);
        }
        
        System.gc(); System.gc(); System.gc();
        long fullMem = rt.totalMemory() - rt.freeMemory();
        
        double memPerKv = (double)(fullMem - emptyMem) / (double) n;
        report = String.format("MEM:%.0f", memPerKv);
        
        db.stop();
        
        return memPerKv;
    }
    
    public static void main(String[] args) {
        MEM m = new MEM();
        m.go();
        System.out.println(m.report);
    }
}
