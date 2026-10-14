package frans;

import java.util.Random;
import bergdb.dag.Node;
import bergdb.dag.ValueNode;

/**
 * Testing performance of high-performance map from
 * long to Node.
 * 
 * @author Frans Lundberg
 */
public class FastMap {
    final Node[][] bins;
    
    public FastMap(int binCount) {
        this.bins = new Node[binCount][];
    }
    
    public void put(long id, Node node) {
        int binIndex = Math.abs((int)(id % bins.length));
        
        Node[] arr = bins[binIndex];
        if (arr == null) {
            arr = new Node[4];
            arr[0] = node;
            bins[binIndex] = arr;
            
        } else {
            for (int i = 0; i < arr.length; i++) {
                if (arr[i] == null) {
                    arr[i] = node;
                }
            }
            
            // NOTE not complete!
        }
    }
    
    public Node get(long id) {
        Node result = null;
        Node[] arr = bins[Math.abs((int)(id % bins.length))];
        if (arr != null) {
            for (int i = 0; i < arr.length; i++) {
                Node node = arr[i];
                if (node == null) {
                    break;
                }
                
                if (node.getSpos() == id) {
                    result = node;
                    break;
                }
            }
        }
        
        return result;
    }
    
    public static void main(String[] args) {
        FastMap m = new FastMap(1000*1000);
        Random r = new Random(0);
        
        long[] ids = new long[2000*1000];
        for (int i = 0; i < ids.length; i++) {
            ids[i] = r.nextLong();
        }
        
        for (int i = 0; i < ids.length; i++) {
            ValueNode v = ValueNode.createDelete();
            v.setSpos(ids[i]);
            m.put(v.getSpos(), v);
        }
        
        long t0 = System.nanoTime();
        long count = 0;
        int reps = 4;
        
        for (int i = 0; i < reps; i++) {
            for (int j = 0; j < ids.length; j++) {
                Node n = m.get(ids[j]);
                if (n != null) count++;
            }
        }
        
        count = count / reps;
        
        double time = (System.nanoTime() - t0) * 1e-9;
        System.out.printf("Time: %.3f s. count:%d.\n", time, count);
        System.out.printf("Time per get: %.3f us.\n", time*1e6 / (reps * ids.length));
    }
}

/*

140721:
Got 0.12 us per lookup. 1M bins, 2M ids.
This test the possibility of using a separate cache. id -> Node. Instead of
the current in-tree cache approach. In-tree cache is super fast, but more dependent
on the rest of the code.

Note that this test is for random access. Actual usage would be better (fewer cache misses).
120 ns ~= 

131129:
Something like 0.12 us per lookup.

*/
