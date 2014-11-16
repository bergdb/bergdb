package bergdb.test;

import java.io.PrintStream;

import bergdb.common.Util;
import bergdb.core.Db;
import bergdb.core.DbUtil;
import bergdb.core.Trans;
import bergdb.nanotest.BasicCollector;
import bergdb.nanotest.TestCollector;
import bergdb.stream.MemoryStream;


/**
 * Let's use check memory with VisualVM or something.
 * Builds key-value map and just waits.
 */
public class PerfDBMem {
     
    public static void get(TestCollector c) {
        int n = 100000;
        int valueSize = 0;
        PrintStream out = c.out();
        Runtime rt = Runtime.getRuntime();        
        Db db = Db.builder().testSetup().mainStream(new MemoryStream()).start();
        
        System.gc(); System.gc(); System.gc();
        long emptyMem = rt.totalMemory() - rt.freeMemory();
        
        int batchSize = 1000;
        for (int i = 0; i < n/batchSize; i++) {
            Trans.Builder b = Db.trans0();
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
        
        System.gc(); System.gc(); System.gc();
        
        int count = 0;
        while (true) {
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
        get(new BasicCollector());
    }
}
