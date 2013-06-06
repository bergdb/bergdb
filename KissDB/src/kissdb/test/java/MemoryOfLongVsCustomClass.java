package kissdb.test.java;

import kissdb.nanotest.TestCollector;
import kissdb.nanotest.T;

/**
 * Tests JVM memory usage for Long and a custom class that has a single
 * "long" field.
 * Test run on rose (32-bit machine), results in same memory usage: 
 * 16 bytes for both. For linda.lemonlog.com, we have 24 bytes for both.
 * This is what to expect 2 pointers (one to object itself, one to class) 
 * + 8 bytes.
 */
public class MemoryOfLongVsCustomClass {
    static String dummy;
    
    @T("perf")
    public static void run(TestCollector c) throws Exception {
        int n = 100 * 1000;
        Object[] longs = new Object[n];
        Object[] pointers = new Object[n];
        
        getMem();
        long mem0 = getMem();
        
        for (int i = 0; i < n; i++) {
            longs[i] = new Long(i);
        }
        
        getMem();
        long mem1 = getMem() - mem0;
        c.report("memPerLong", ((double) mem1) / n);
        
        getMem();
        mem0 = getMem();
        
        for (int i = 0; i < n; i++) {
            pointers[i] = new StreamPointer(i);
        }
        
        getMem();
        mem1 = getMem() - mem0;
        c.report("memPerCustomObject", ((double) mem1) / n);
        
        int index = (int) (Math.random() * n);
        dummy = longs[index] + "-" + pointers[index];
            // To avoid compiler optimizations, arrays must be used.
    }
    
    /** 
     * Returns memory usage in bytes.
     */
    private static long getMem() throws InterruptedException {
        System.gc();
        Thread.sleep(100);
        System.gc();
        Thread.sleep(100);
        Runtime rt = Runtime.getRuntime();        
        return rt.totalMemory() - rt.freeMemory();
    }
    
    private static class StreamPointer {
        public long spos;
        
        public StreamPointer(long spos) {
            this.spos = spos;
        }
        
        public long getSSPos() {
            return spos;
        }
        
        public String toString() {
            return "" + getSSPos();
        }
    }
}

/*
2012-05
$ java -cp p/KissDB/ -server -Xmx1000m com.kissdb.main.RunPerf "com.kissdb.perf.MemoryOfLongVsCustomClass"
com.kissdb.perf.MemoryOfLongVsCustomClass.run.memPerLong: 16.012
com.kissdb.perf.MemoryOfLongVsCustomClass.run.memPerCustomObject: 16.00448
*/