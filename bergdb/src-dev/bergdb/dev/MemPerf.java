package bergdb.dev;

import java.io.PrintStream;

import bergdb.common.Util;
import bergdb.core.Db;
import bergdb.core.DbUtil;
import bergdb.core.Trans;
import bergdb.nanotest.SimpleTestEnvironment;
import bergdb.nanotest.TestEnvironment;
import bergdb.stream.DummyStream;

/**
 * Executable class that created 1M small KVs and analyses total
 * memory usage per KV. The main method does not exit, it keeps
 * running. Suitable for analysis the live in-memory structure 
 * with VisualVM.
 * 
 * @author Frans Lundberg
 */
public class MemPerf {
     
    public static void get(TestEnvironment c) {
        int n = 1000*1000;
        int valueSize = 0;
        PrintStream out = c.out();
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

        c.report("n", n);
        c.report("valueSize", valueSize);
        c.report("emptyMem", emptyMem);
        
        int count = 0;
        while (true) {
            System.gc(); System.gc(); System.gc();
            
            long used = rt.totalMemory() - rt.freeMemory();
            out.println("Doing nothing " + (count++));
            out.println("  maxMemory: " + rt.maxMemory());
            out.println("  totalMemory: " + rt.totalMemory());
            out.println("  freeMemory: " + rt.freeMemory());
            out.println("  used: " + used);
            
            double memPerKV = (double)(used - emptyMem) / (double) n;
            out.println("  memPerKV: " + memPerKV);
            
            try {
                Thread.sleep(10000);
            } catch (InterruptedException e) {
                break;
            }
            
            if (count % 1000 == 999) {
                DbUtil.get(db, 99999, Util.toBytes("hej!"));
            }
        }
    }
    
    public static void main(String[] args) throws Exception {
        get(new SimpleTestEnvironment());
    }
}

/*

150106 Frans: memPerKv: 161 (cissi, Oracle JVM 7, 1M KVs)

*/
