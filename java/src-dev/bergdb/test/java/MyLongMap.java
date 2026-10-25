package bergdb.test.java;

import java.util.Random;
import bergdb.common.HashUtil;
import bergdb.nanotest.Nano;
import bergdb.nanotest.SimpleTestEnvironment;
import bergdb.nanotest.TestEnvironment;

/**
 * Map performance testing; what would be the performance of a long-to-Node 
 * specialized hash map implementation be? 
 * BergDB case is to use id-to-node lookups for every followPointer 
 * operation, instead of following Java reference like today.
 * Of course, this approach add delay, but a 1-in-1M HashMap lookup is
 * only 48 ns (tested today, on cissi, 2017-07-31, i7 at 2.1 GHz, JVM 8, Ubuntu).
 * 
 * @author Frans Lundberg
 */
public class MyLongMap {
    static final int binCount = 2*1048576;
            // fixed at 2^21 for this test, test with 1M entries for 0.50 fill factor
    final Node[] table;
    
    // test data
    long[] testKeys;
    Node[] testValues;
    
    /**
     * A new instance with the given number of 
     */
    public MyLongMap() {
        table = new Node[binCount];
    }
    
    /**
     * Puts unconditionally, does not check if value is in the bin there already.
     */
    public void put(long id, Node value) {
        assert value != null;
        int index = index3(id);
        value.next = table[index];
        table[index] = value;
    }
    
    public final Node get(long id) {
        Node node = table[index3(id)];
        while (node != null) {
            if (node.id == id) {
                return node;
            }
            node = node.next;
        }
        return null;
    }
    
    @SuppressWarnings("unused")
    private final int index1(long key) {
        return HashUtil.mHashIndex(key, binCount);
    }

    @SuppressWarnings("unused")
    private final int index2(long x) {
        x = (x ^ (x >>> 30)) * 0xbf58476d1ce4e5b9L;
        x = (x & 0x7fffffff) % binCount;
        return (int) x;
    }
    
    private final int index3(long x) {
        x = (x ^ (x >>> 30)) * 0xbf58476d1ce4e5b9L;
        x = (x ^ (x >> 27)) * 0x94d049bb133111ebL;
        x = x ^ (x >> 31);
        return (int) (x & 0x7fffffff) % binCount;
    }
    
    /**
     * Generates and puts test data into the map.
     */
    private void generateTestData(int n) {
        Random random = new Random(1);
        testKeys = new long[n];
        testValues = new Node[n];
        
        for (int i = 0; i < n; i++) {
            int anInt = random.nextInt();
            long id = anInt;
            Node node = new Node();
            node.id = id;
            node.spos = id;
            testKeys[i] = id;
            testValues[i] = node;
        }
        
        for (int i = 0; i < testKeys.length; i++) {
            put(testKeys[i], testValues[i]);
        }
    }
    
    @Nano("perf")
    public static void go(TestEnvironment r) {
        MyLongMap m = new MyLongMap();
        int n = 1000*1000;
        m.generateTestData(n);
        
        r.out().println("Starting, get...");
        int reps = 10;
        long t0 = System.nanoTime();
        for (int i0 = 0; i0 < reps; i0++) {
            for (int i = 0; i < n; i++) {
                m.get(m.testKeys[i]);
                //Node value = m.get(m.testKeys[i]);
                //if (value.id != m.testKeys[i]) {
                //    throw new Error("not expected");
                //}
            }
        }
        long t1 = System.nanoTime();
        
        double totalTime = (t1 - t0) * 1e-9;
        r.report("n", n);
        r.report("ns-per-get", (totalTime / (reps*n))*1e9);
        r.report("total-time", totalTime);
    }
    
    public static void main(String[] args) throws Exception {
        go(new SimpleTestEnvironment());
    }

    public static class Node {
        public Node next;
        public long id;
        public long spos;
        public long[] klongs;
        public long[] pointers;
    }
}
