package bergdb.test.manual;

import java.io.PrintStream;
import java.util.Random;

import bergdb.core.Db;
import bergdb.core.KeyFactory;
import bergdb.core.NoEvictBoss;
import bergdb.core.Trans;
import bergdb.nanotest.T;
import bergdb.nanotest.TestCollector;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.MemoryStream;

/**
 * This test investigates how the startup distance, L, affects the stream size.
 * 
 * @author Frans Lundberg
 */
public class StreamSizeVsStartupDistance {

    @T("perf")
    public static void t1(TestCollector c) {
        PrintStream out = c.out();
        //int startupDistance = 1000*1000000;
        //int startupDistance = 100*1000000;
        //int startupDistance = 30*1000000;
        //int startupDistance = 10*1000000;
        //int startupDistance = 3*1000000;
        //int startupDistance = 1*1000000;
        int startupDistance = 300*1000;
        //int startupDistance = 100*1000;
        //int startupDistance = 10*1000;
        //int startupDistance = 1*1000;
        //int startupDistance = 100;
        
        AppendOnlyStream stream = new MemoryStream();
        //AppendOnlyStream stream = new NullStream();
        Db db = Db.builder().mainStream(stream).startupDistance(startupDistance)
                .evictBoss(new NoEvictBoss()).retainForever().start();
        
        int n = 1000*1000;
        int batchSize = 100;
        byte[] empty = new byte[0];
        
        assert n % batchSize == 0;
        int index = 0;
        
        for (int i = 0; i < n/batchSize; i++) {
            Trans.Builder b = Trans.builder();
            
            for (int j = 0; j < batchSize; j++) {
                b.set(KeyFactory.binaryIntKey(index), empty);
                index++;
            }
            
            db.execute(b.build());
        }
        
        long streamSize1 = db.getStreamLength();
        double sizePerKV = ((double) streamSize1) / n;
        
        out.println("Created database of size " + n + ".");
        out.println("startupDistance = " + startupDistance);
        out.println("Stream size per KV: " + sizePerKV);
        
        Random random = new Random(0);
        
        // Start random writes.
        
        int tCount = 100*1000;
        
        for (int i = 0; i < tCount; i++) {
            index = random.nextInt(n);
            db.execute(Trans.builder().set(KeyFactory.binaryIntKey(index), empty).build());
        }
        
        long addedSize = db.getStreamLength() - streamSize1;
        double addedSizePerKV = ((double) addedSize) / tCount;
        out.println("Total stream size: " + db.getStreamLength());
        out.println("Updated " + tCount + " key-value pairs.");
        out.println("Additional size per KV: " + addedSizePerKV);
    }
}

/*

---- 120913 ----

n = 1000*1000; batchSize = 100*1000 (should not matter). Updating 100*1000 random kvs each in 
a transaction of their own.

startupDistance,   addedSizePerKV, factor
100,               1519, 4.31
1000,              1344, 3.81
10000,             1067, 3.03
100000,             853, 2.42
300000,             754, 2.14
1000000,            648, 1.84
3000000,            544, 1.55
10000000,           427, 1.21
30000000,           381, 1.08
100000000,          358, 1.02
1000000000,         352, 1.00

Plot with QtiPlot or something.
*/