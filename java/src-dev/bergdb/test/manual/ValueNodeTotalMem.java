package bergdb.test.manual;

import java.util.concurrent.atomic.AtomicLong;

import bergdb.nanotest.CommandLine;

/**
 * Tests a method to keep an estimate of the memory consumption 
 * of all value nodes.
 * 
 * @author Frans Lundberg
 */
public class ValueNodeTotalMem {
    final AtomicLong totalMem = new AtomicLong();
    final AtomicLong totalCount = new AtomicLong();

    public static void main(String[] args) throws Exception {
        new ValueNodeTotalMem().go(args);
    }
    
    private void go(String[] args) throws InterruptedException {
        CommandLine line = new CommandLine(args);
        
        int n = 100;
        if (line.hasOne("n")) {
            n = Integer.parseInt(line.getOne("n"));
        }
        
        MemListener listener = new MemListener() {
            public void reportChange(int countDelta, int sizeDelta) {
                totalMem.addAndGet(sizeDelta);
                totalCount.addAndGet(countDelta);
            }
        };
        
        MyValueNode[] nodes = new MyValueNode[n];
        for (int i = 0; i < n; i++) {
            nodes[i] = new MyValueNode(new byte[20], listener);
        }
        
        System.gc();
        printTotals();
        
        for (int i = 0; i < n; i++) {
            if (i % 2 == 0) {
                nodes[i] = null;
            }
        }
        
        System.gc();
        Thread.sleep(500);
        printTotals();
        
        for (int i = 0; i < n; i++) {
            nodes[i] = null;
        }
        
        System.gc();
        Thread.sleep(500);
        printTotals();
        
        Thread.sleep(1000);
        System.gc();
        printTotals();
        
    }
    
    private void printTotals() {
        System.out.println("totalMem: " + totalMem.get() + ", " + totalCount);
    }

    public static class MyValueNode {
        // Assumption: computeMemSize() always return the same value.
        final MemListener memListener;
        final byte[] value;
        
        public MyValueNode(byte[] value, MemListener memListener) {
            this.memListener = memListener;
            this.value = value;
            memListener.reportChange(+1, computeMemSize());
        }
        
        public int computeMemSize() {
            return value.length + 16 + 8;
        }
        
        protected void finalize() throws Throwable {
            memListener.reportChange(-1, -computeMemSize());
            super.finalize();
        }
    }
    
    public static interface MemListener {
        /** Reports that the memory consumption descresed. */
        public void reportChange(int countDelta, int sizeDelta);
    }
}
