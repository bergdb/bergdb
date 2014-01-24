package frans;

import java.util.Random;

import bergdb.dag.INode;
import bergdb.dag.ValueNode;

// TODO E. finish this. Check performance.

/**
 * Testing performance of high-performance map from
 * long to INode.
 */
public class FastMap {
    final INode[][] bins;
    
    public FastMap(int binCount) {
        this.bins = new INode[binCount][];
    }
    
    public void put(long id, INode node) {
        int binIndex = Math.abs((int)(id % bins.length));
        
        INode[] arr = bins[binIndex];
        if (arr == null) {
            arr = new INode[4];
            arr[0] = node;
            bins[binIndex] = arr;
            
        } else {
            for (int i = 0; i < arr.length; i++) {
                if (arr[i] == null) {
                    arr[i] = node;
                }
            }
            
            // of course not complete
        }
    }
    
    public INode get(long id) {
        INode result = null;
        INode[] arr = bins[Math.abs((int)(id % bins.length))];
        if (arr != null) {
            for (int i = 0; i < arr.length; i++) {
                INode node = arr[i];
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
            ValueNode v = new ValueNode();
            v.spos = ids[i];
            m.put(v.spos, v);
        }
        
        long t0 = System.nanoTime();
        long count = 0;
        int reps = 4;
        
        for (int i = 0; i < reps; i++) {
            for (int j = 0; j < ids.length; j++) {
                INode n = m.get(ids[j]);
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

131129:
Something like 0.12 us per lookup.

*/
