package bergdb.test;

import java.io.IOException;

import bergdb.core.DatabaseId;
import bergdb.core.Db;
import bergdb.core.KTestClock;
import bergdb.core.KeyFactory;
import bergdb.core.NodeStream;
import bergdb.core.Trans;
import bergdb.nanotest.T;
import bergdb.nanotest.TestCollector;
import bergdb.stream.MemoryStream;


/**
 * Checks whether the database stream is deterministic.
 * 
 * @author Frans Lundberg
 */
public class IsDeterministic {

    /** 
     * Tests DB as empty as it gets.
     */
    @T("f")
    public static void testEmptyDB(TestCollector c) throws IOException {
        MemoryStream first = null;

        for (int i = 0; i < 1+5; i++) {
            MemoryStream m = new MemoryStream();
            Db db = Db.builder().testSetup().mainStream(m).id(DatabaseId.getTestId()).start();
            db.sync();
            
            if (i == 0) {
                first = m;
            } else {
                compareStreams(first, m, i);
            }
            
            db.stop();
            db = null;
        }
    }
    
    /** 
     * Tests DB with one KV.
     */
    @T("f")
    public static void testOneKV(TestCollector c) throws IOException {
        MemoryStream first = null;
        NodeStream firstNodeStream = null;
        
        for (int i = 0; i < 1+3; i++) {
            MemoryStream m = new MemoryStream();
            KTestClock clock = new KTestClock();
            Db db = Db.builder().testSetup().mainStream(m).clock(clock).id(DatabaseId.getTestId()).start();
            clock.setTime(100);
            db.execute(Trans.builder().set("k", "v"));
            db.sync();
            
            if (i == 0) {
                first = m;
                firstNodeStream = (NodeStream) db.getStream();
            } else {
                try {
                    compareStreams(first, m, i);
                } catch (AssertionError e) {
                    NodeStream mNodeStream = (NodeStream) db.getStream();
                    
                    c.out().println("======== IsDeterministic.testOneKV, first ========");
                    firstNodeStream.printStream(System.out);
                    
                    c.out().println("======== IsDeterministic.testOneKV, m, i=" + i + " ========");
                    mNodeStream.printStream(System.out);
                    
                    throw e;
                }
            }
            
            db.stop();
            db = null;
        }
    }
    
    /** 
     * Tests DB with multiple KVs.
     */
    @T("f")
    public static void testMultipleTransactions(TestCollector c) throws IOException {
        MemoryStream first = null;
        NodeStream firstNodeStream = null;
        
        for (int i = 0; i < 1+3; i++) {
            MemoryStream m = new MemoryStream();
            KTestClock clock = new KTestClock();
            Db db = Db.builder().testSetup().mainStream(m).clock(clock).id(DatabaseId.getTestId()).start();
            
            for (int j = 0; j < 10; j++) {
                clock.setTime(100 + j*10);
                Trans.Builder b = Trans.builder();
                b.set(KeyFactory.crazyKey(j*2), new byte[j]);
                b.set(KeyFactory.crazyKey(j*2 + 1), new byte[j]);
                db.execute(b);
            }
            db.sync();
            
            if (i == 0) {
                first = m;
                firstNodeStream = (NodeStream) db.getStream();
            } else {
                try {
                    compareStreams(first, m, i);
                } catch (AssertionError e) {
                    NodeStream mNodeStream = (NodeStream) db.getStream();
                    
                    c.out().println("======== IsDeterministic.testMultipleTransactions, first ========");
                    firstNodeStream.printStream(System.out);
                    
                    c.out().println("======== IsDeterministic.testMultipleTransactions, m, i=" + i + " ========");
                    mNodeStream.printStream(c.out());
                    
                    throw e;
                }
            }
            
            db.stop();
            db = null;
        }
    }
    
    private static void compareStreams(MemoryStream first, MemoryStream m, int run) throws IOException {
        if (first.getLength() != m.getLength()) {
            throw new AssertionError("Stream sizes differ, " + first.getLength() 
                    + ", " + m.getLength());
        }
        
        byte[] buffer1 = new byte[1000];
        byte[] buffer2 = new byte[buffer1.length];
        long offset = 0;
        
        while (true) {
            long bytesToRead = first.getLength() - offset;
            if (bytesToRead <= 0) {
                break;
            }
            
            if (bytesToRead > buffer1.length) {
                bytesToRead = buffer1.length;
            }
            
            first.read(offset, buffer1, 0, (int) bytesToRead);
            m.read(offset, buffer2, 0, (int) bytesToRead);
            offset += bytesToRead;
            
            for (int i = 0; i < (int) bytesToRead; i++) {
                if (buffer1[i] != buffer2[i]) {
                    throw new AssertionError("Mem streams differ at " + (offset + i) 
                            + " for run " + run + ".");
                }
            }
        }
    }
}
