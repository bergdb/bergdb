package bergdb.test.manual;

import java.io.PrintStream;

import bergdb.core.Db;
import bergdb.core.KeyFactory;
import bergdb.core.NoEvictBoss;
import bergdb.core.Trans;
import bergdb.stream.MemoryStream;

/**
 * <p>Checks the stream size for a database with 1M entries.
 * Introduced when trying a kv-based stream instead of the current node-based
 * approach (131130). The current implementation (with stream in memory) 
 * requires 1-2 GB RAM.</p>
 * 
 * <p>For cases are investigated: 1. storing 1M small entries in insert-order, 
 * 2. storing 1M entries, not in insert-order.</p>
 * 
 * @author Frans Lundberg
 */
public class StreamSizeFourCases {
    Db db;
    byte[][] keys;
    byte[] value;
    int n = 1000*1000;
    
    public StreamSizeFourCases() {
        value = new byte[100];
    }
    
    void createDatabase() {
        MemoryStream stream = new MemoryStream();
        db = Db.builder().mainStream(stream).evictBoss(new NoEvictBoss()).retainForever().start();
    }
    
    void createKeysForCase1() {
        keys = new byte[n][];
        
        for (int i = 0; i < n; i++) {
            keys[i] = KeyFactory.binaryIntKey(i);
        }
    }
    
    void createKeysForCase2() {
        keys = new byte[n][];
        
        for (int i = 0; i < n; i++) {
            keys[i] = KeyFactory.binaryIntKeyLE(i);
        }
    }
    
    void runOneByOne() {
        createDatabase();
        for (int i = 0; i < n; i++) {
            db.execute(Trans.builder().put(keys[i], value));
        }
        
        db.sync();
        long length = db.getStreamLength();
        System.out.printf("Stream size: %d bytes, %.1f MB.\n", length, length / 1000.0);
    }
    
    void runBatches() {
        createDatabase();
        int batchSize = 1000;
        int reps = n / batchSize;
        
        for (int i = 0; i < reps; i++) {
            Trans.Builder b = Trans.builder();
            
            for (int j = 0; j < batchSize; j++) {
                b.put(keys[i * batchSize + j], value);
            }
            
            db.execute(b.build());
        }
        
        db.sync();
        long length = db.getStreamLength();
        System.out.printf("Stream size: %d bytes, %.1f MB.\n", length, length / 1000.0);
    }
    
    public static void main(String[] args) {
        StreamSizeFourCases s = new StreamSizeFourCases();
        PrintStream out = System.out;
        
        out.println("---- Four cases ----");
        s.createDatabase();
        out.println("startupDistance: " + s.db.getStartupDistance());
        out.println();
        
        out.println("---- case1A() ----");
        out.println("Ordered keys, one-by-one.");
        s.createKeysForCase1();
        s.runOneByOne();
        System.gc();
        
        out.println("---- case1B() ----");
        out.println("Ordered keys, batches.");
        s.createKeysForCase1();
        s.runBatches();
        System.gc();
        
        out.println("---- case2A() ----");
        out.println("Unordered keys, one-by-one.");
        s.createKeysForCase2();
        s.runOneByOne();
        System.gc();
        
        out.println("---- case2B() ----");
        out.println("Unordered keys, batches.");
        s.createKeysForCase2();
        s.runBatches();
        System.gc();
    }
}

/*

131130
======

Release 2013.3. Output:
    ---- Four cases ----
    startupDistance: 20000000
    ---- case1A() ----
    Ordered keys, one-by-one.
    Stream size: 690741912 bytes, 690741.9 MB.
    ---- case1B() ----
    Ordered keys, batches.
    Stream size: 314874152 bytes, 314874.2 MB.
    ---- case2A() ----
    Unordered keys, one-by-one.
    Stream size: 850441088 bytes, 850441.1 MB.
    ---- case2B() ----
    Unordered keys, batches.
    Stream size: 688486208 bytes, 688486.2 MB.

KV size: 1000000*(4+4 + 4+100) = 112000000 = 112M.
This should be a reasonable base case for comparison when trying a KV-based stream format
instead.
    
*/
