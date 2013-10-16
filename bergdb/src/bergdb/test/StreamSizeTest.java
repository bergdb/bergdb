package bergdb.test;

import bergdb.core.Db;
import bergdb.core.Trans;
import bergdb.coreds.Keys;
import bergdb.nanotest.BasicCollector;
import bergdb.nanotest.T;
import bergdb.nanotest.TestCollector;
import bergdb.stream.MemoryStream;

/**
 * Standard test to check that overhead of stream does not grow significantly.
 * 
 * @author Frans Lundberg
 */
public class StreamSizeTest {
    
    private static long[] key(int index) {
        return Keys.toSegments("/k" + index);
    }

    @T("perf")
    public static void run(TestCollector c) {
        MemoryStream stream = new MemoryStream();
        Db db = Db.builder().mainStream(stream).start();
        
        byte[] v1 = new byte[0];
        byte[] v2 = new byte[1000];
        int index = 0;
        
        for (int i = 0; i < 50*1000; i++) {
            db.execute(Trans.builder().put(key(index), v1));
            index += 1;
        }
        
        for (int i = 0; i < 1*1000; i++) {
            Trans.Builder b = Trans.builder();
            
            for (int j = 0; j < 50; j++) {
                b.put(key(index), v1);
                index += 1;
            }
            
            db.execute(b.build());
        }
        
        for (int i = 0; i < 5*1000; i++) {
            db.execute(Trans.builder().put(key(index), v2));
            index += 1;
        }
        
        for (int i = 0; i < 50*1000; i++) {
            db.execute(Trans.builder().put(key(index), v1));
            index += 1;
        }
        
        db.sync();
        c.report("length", db.getStreamLength());
        c.report("nodesWritten", db.getNodesWritten());
        c.report("dirtyFraction", db.getDirtyFraction1000());
    }
    
    public static void main(String[] args) {
        run(new BasicCollector());
    }
}

/*

Branch 2013:
$ time j -ea bergdb.test.StreamSizeTest
* length: 60207632
* nodesWritten: 387470

Branch "forward-pointers":
$ time j -ea bergdb.test.StreamSizeTest
* length: 97182920
* nodesWritten: 545899

*/
