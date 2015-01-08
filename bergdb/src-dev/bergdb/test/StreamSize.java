package bergdb.test;

import bergdb.core.Db;
import bergdb.core.DbBuilder;
import bergdb.core.KeyFactory;
import bergdb.core.SyncLevel;
import bergdb.core.Trans;
import bergdb.nanotest.BasicTestEnvironment;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.stream.MemoryStream;


/**
 * Tests the stream size overhead per KV and per transaction.
 * 
 * @author Frans Lundberg
 */
public class StreamSize {
    
    @Nano("perf")
    public static void transStreamOverhead(TestEnvironment c) {
        int[] kvSizes = new int[] {100*1000, 10*1000, 1000,  100,  4};
        int[] kvCount = new int[] {100,      100,     100,   100,  100};
        
        c.report("note", "Runs each KV in a separate transaction. KV sizes varies from 0.1M to 4. 100 KVs per run.");

        for (int i = 0; i < kvSizes.length; i++) {
            MemoryStream m = new MemoryStream();
            Db db = Db.builder().mainStream(m).start();
            
            c.report("run" + i + "-kvSize", kvSizes[i]);
            c.report("run" + i + "-kvCount", kvCount[i]);
            
            for (int j = 0; j < kvCount[i]; j++) {
                byte[] value = new byte[kvSizes[i] - 4];
                db.execute(db.trans().put(KeyFactory.binaryIntKey(j), value).build());
            }
            db.sync(SyncLevel.ORDINARY);
            
            double overheadPerKV = (m.getLength() - kvCount[i]*kvSizes[i]) / ((double) kvCount[i]);
            overheadPerKV = Math.round(overheadPerKV * 10) / 10.0;
            
            c.report("run" + i + "-stream-size", m.getLength());
            c.report("run" + i + "-overhead-per-KV", overheadPerKV);
        }
    }
    
    @Nano("perf")
    public static void kvStreamOverhead(TestEnvironment c) {
        
        c.report("notes", "Finds minimum stream overhead per KV.");
        
        byte[] value = new byte[0];
        
        for (int n = 2; n < 10; n++) {
            MemoryStream m = new MemoryStream();
            Db db = Db.builder().mainStream(m).start();
            Trans.Builder b = db.trans();
            for (int k = 0; k < n; k++) {
                b.put(KeyFactory.binaryIntKey(k), value);
            }
            Trans trans = b.build();
            db.execute(trans);
            long size1 = trans.lastPos - trans.pos + 1;
            
            
            m = new MemoryStream();
            db = Db.builder().mainStream(m).start();
            b = db.trans();
            for (int k = 0; k < n + 1; k++) {
                b.put(KeyFactory.binaryIntKey(k), value);
            }
            trans = b.build();
            db.execute(trans);
            long size2 = trans.lastPos - trans.pos + 1;
            
            c.report("overhead-" + n, size2 - size1);
        }
    }
    
    @Nano("perf")
    public static void t3(TestEnvironment c) {
        c.report("notes", "Average transaction stream size vs maxNodeSize");
        
        DbBuilder[] builders = new DbBuilder[] {
                Db.builder().maxNodeSize8(),
                Db.builder().maxNodeSize14(),
                Db.builder().maxNodeSize30(),
                Db.builder().maxNodeSize62()
        };
        
        int[] sizes = new int[]{8, 14, 30, 62};
        
        byte[] value = new byte[0];
        long sum;
        int n = 100;
        
        for (int idb = 0; idb < builders.length; idb++) {
            Db db = builders[idb].mainStream(new MemoryStream()).start();
            sum = 0;
            
            for (int i = 0; i < n; i++) {
                Trans trans = db.trans().put("" + i, value).build();
                db.execute(trans);
                long size = (trans.lastPos - trans.pos + 1);
                sum += size;
            }
            
            c.report("averageSize-" + sizes[idb], (sum / n));
        }
    }
    
    public static void main(String[] args) {
        //transStreamOverhead(new BasicTestEnvironment());
        //kvStreamOverhead(new BasicTestEnvironment());
        t3(new BasicTestEnvironment());
    }
}
