package bergdb.dev;

import java.io.File;
import java.util.Random;
import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.dag.GetMany.StopCondition;
import bergdb.common.Bytes;
import bergdb.core.Db;
import bergdb.core.Trans;
import bergdb.stream.FileStream;

/**
 * Demo class, Google Queen
 * 
 * @author Frans Lundberg
 */
public class GoogleQueen {
    
    
    void go() throws Exception {
        FileStream stream = new FileStream(new File("/a/temp/queen-test"));
        
        long t0 = System.nanoTime();
        Db db = Db.builder().mainStream(stream).startupDistance(40*1000000).start();
        long t1 = System.nanoTime();
        
        System.out.println("Started, startup time: " + 1e-9*(t1-t0));
        
        //createData(db);        
        // getPerformance(db);
        // putPerformance(db);
        seqPerformance(db);
        seqPerformance(db);
        seqPerformance(db);
        
    }
    
    void seqPerformance(Db db) {
        long t1 = System.nanoTime();
        long[] startKey = Keys.toSegments(new byte[0]);
        GetMany g;
        boolean firstBatch = true;
        long count = 0;
        
        System.out.println("seqPerformance");
        
        while (true) {
            IterStopCondition stopCondition = new IterStopCondition();            
            g = db.newGetMany();
            g.startKey = startKey;
            g.forward = true;
            g.inclusive = firstBatch ? true : false;
            g.stopCondition = stopCondition;
            g.lookupTime = Long.MAX_VALUE;
            
            db.getMany(g);
            count += g.result.size();
            
            if (g.result.size() > 0) {
                startKey = g.result.get(g.result.size() - 1).key;
            }
            
            if (firstBatch) {
                firstBatch = false;
            }
            
            if (stopCondition.gotEod()) {
                break;
            }
        }
        
        long t2 = System.nanoTime();
        double time = 1e-9 * (t2 - t1);
        double timePerEntry = time / count;
        
        System.out.println("seq, time: " + time + ", time per entry: " + timePerEntry);
    }
    
    
    /**
     * Max 100 KVs.
     */
    private class IterStopCondition implements GetMany.StopCondition {
        private static final int maxCount = 1000;
        private boolean isFirst;
        private int count = 0;
        private boolean gotEod = false;
        
        public IterStopCondition() {
            isFirst = true;
            gotEod = false;
        }
        
        public int handleKvt(Kvt kvt) {
            int result = StopCondition.ADD;     // default result
            count++;
            
            if (count >= maxCount) {
                result = GetMany.StopCondition.ADD_AND_STOP;
            }
        
            return result;
        }

        public void eod() {
            gotEod = true;
        }
        
        public final boolean gotEod() {
            return gotEod;
        }
    }
    
    void putPerformance(Db db) {
        int n = 100000;
        long[][] keys1 = createRandomKeys(n);
        long[][] keys2 = createRandomKeys(n);
        int transSize = 100;
        long t0, t1, t2;
        double time;
        
        System.out.println("putPerformance");
        
        t0 = System.nanoTime();
        
        for (int i = 0; i < n / transSize; i++) {
            Trans.Builder builder = new Trans.Builder();
            for (int j = 0; j < transSize; j++) {
                builder.put(keys1[i * transSize + j], new byte[8]);
            }
            db.execute(builder.build());
        }
        
        t1 = System.nanoTime();
        time = 1e-9 * (t1 - t0);
        System.out.println("Time: " + time + ", time per PUT: " + (time/n));
        
        t1 = System.nanoTime();
        
        for (int i = 0; i < n / transSize; i++) {
            Trans.Builder builder = new Trans.Builder();
            for (int j = 0; j < transSize; j++) {
                builder.put(keys2[i * transSize + j], new byte[8]);
            }
            db.execute(builder.build());
        }
        
        t2 = System.nanoTime();
        time = 1e-9 * (t2 - t1);
        System.out.println("Time: " + time + ", time per PUT: " + (time/n));
    }
    
    void getPerformance(Db db) {
        GetData gd = db.newGetData();
        int n = 100000;
        long[][] keys1 = createRandomKeys(n);
        long[][] keys2 = createRandomKeys(n);
        
        System.out.println("getPerformance");
        
        for (int i = 0; i < n; i++) {
            db.getOne(Long.MAX_VALUE, keys1[i], gd);
        }
        
        long t0 = System.nanoTime();
        
        for (int i = 0; i < n; i++) {
            db.getOne(Long.MAX_VALUE, keys2[i], gd);
        }
        
        long t1 = System.nanoTime();
        double time = 1e-9 * (t1 - t0);
        
        System.out.println("Time: " + time + ", time per GET: " + (time/n));
    }
    
    long[][] createRandomKeys(int n) {
        long[][] keys = new long[n][];
        byte[] keyBytes = new byte[8];
        Random random = new Random(0);
        
        for (int i = 0; i < keys.length; i++) {
            int index = random.nextInt(25*1000000);
            Bytes.longToBytesBE(index, keyBytes, 0);
            keys[i] = Keys.toSegments(keyBytes);
        }
        return keys;
    }
    
    void createData(Db db) {
        int total = 25*1000000;
        int transSize = 100;
        int transCount = total / transSize;
        byte[] keyBytes = new byte[8];
        
        System.out.println("Creating " + total + " entries in " + transCount + " transactions.");
        
        for (int i = 0; i < transCount; i++) {
            byte[] valueBytes = new byte[8];
            
            Trans.Builder builder = new Trans.Builder().put(keyBytes, valueBytes);
            for (int j = 0; j < transSize; j++) {
                Bytes.longToBytesBE(i*transSize + j, keyBytes, 0);
                builder.put(keyBytes, valueBytes);
            }            
            db.execute(builder.build());
            
            if (i % 1000 == 0) {
                System.out.println("Trans " + i);
            }
        }
    }
    
    public static void main(String[] args) throws Exception {
        new GoogleQueen().go();
    }
}

/*

Testing for Google Queen. On (old) Cissi laptop.
25 M key-value (8 -> 8 bytes) on each storage server.
10 billion entries on 400 servers.

Per second...
Reads: 20M -- 50k/s per node.
Writes: 20M -- 50k/s per node.
Data ops: 40M -- 100k/s per node (10 us per op).

Data size: 2.5 GB. Per entry: 2.5e9 / 25e6 = 100.

Startup time: 3.0 s.
GET time: 2.3 us per get. Nice! Within the 10 us requirement.

PUT time: 3.1 us per PUT.

CONCLUSION: works! But, notice the large data amount. 
Each data node will grown with 50k writes per second.
Maybe 200 bytes per write (random writes) -> 10 M/s.
Per hour: 36 GB. Much larger than the original database!
Short history, will reclaim work? Will it keep up?
It should work for one hour substained rate.

*/
