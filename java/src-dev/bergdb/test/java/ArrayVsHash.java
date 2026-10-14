package bergdb.test.java;

import java.util.HashMap;
import java.util.Random;

import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;

/**
 * Tests storing key-value data in a hash maps versus a simple array.
 * 
 * @author Frans Lundberg
 */
public class ArrayVsHash {
    private Long[] keys;
    private long[] primaryKeys;
    private String[] values;
    private HashMap<Long, String> map;
    
    @Nano("perf")
    public static void run(TestEnvironment c) throws Exception {
        new ArrayVsHash().go(c);
    }
    
    @SuppressWarnings("unused")
    public void go(TestEnvironment c) throws Exception {
        Random random = new Random(0);
        int current = 0;
        long t0, t1;
        
        //keys = new Long[100];
        keys = new Long[1000];
        //keys = new Long[10000];
        
        map = new HashMap<Long, String>(keys.length);
        values = new String[keys.length];
        primaryKeys = new long[keys.length];
        
        for (int i = 0; i < keys.length; i++) {
            current += (int) (1.5 * random.nextDouble());
            primaryKeys[i] = current;
            keys[i] = new Long(current);
            values[i] = "value:" + i;
            map.put(keys[i], values[i]);
        }
        
        String s = null;
        double time;
        long[] lookups = new long[10000];
        
        random.setSeed(0);
        current = 0;
        
        for (int i=0; i<lookups.length; i++) {
            current += (int) (1.5 * random.nextDouble());
            lookups[i] = current;
        }
        
        c.report("size", keys.length);
        
        t0 = System.nanoTime();
        for (int i = 0; i < lookups.length; i++) {
            s = getFromHash(lookups[i]);
        }
        t1 = System.nanoTime();
        time = (t1-t0) * 1e-9;
        c.report("timeHash", time/lookups.length);
        
        t0 = System.nanoTime();
        for (int i = 0; i < lookups.length; i++) {
            s = getFromArray(lookups[i]);
        }
        t1 = System.nanoTime();
        time = (t1-t0) * 1e-9;
        c.report("timeArray", time/lookups.length);
        
        
        t0 = System.nanoTime();
        for (int i = 0; i < lookups.length; i++) {
            s = getFromPrimaryArray(lookups[i]);
        }
        t1 = System.nanoTime();
        time = (t1-t0) * 1e-9;
        
        c.report("timePrimaryArray", time/lookups.length);
    }

    private String getFromHash(Long key) {
        return map.get(key);
    }
    
    private String getFromArray(Long key) {
        for (int i = 0; i < keys.length; i++) {
            if (key.equals(keys[i])) {
                return values[i];
            }
        }
        return null;
    }
    
    private String getFromPrimaryArray(long key) {
        for (int i = 0; i < primaryKeys.length; i++) {
            if (primaryKeys[i] == key) {
                return values[i];
            }
        }
        return null;
    }
}

/*


Comments 080816
===============

The primitive array is around a factor of 2.0 faster than the object version.
The HashMap is faster for a size of 1000, but only 3 times faster then the
primitive array version. The primitive array version is faster (3 times) for a size of 100.
A general rule of thumb is:
If a collection contains more than 100 to 1000 objects, use hash lookups 
(or tree or something faster than no index).
These tests assume a very fast key comparison method. This is not always the
case. For slower key comparisons, the size when to switch to a hash map will
be lower.

*/
