package bergdb.test.java;

import java.util.Map;
import java.util.Random;
import java.util.TreeMap;
import bergdb.common.ByteArrayComparator;
import bergdb.common.StringUtil;
import bergdb.nanotest.SimpleTestEnvironment;
import bergdb.nanotest.Nano;

/**
 * Performance of get-operation from a TreeMap.
 * 
 * @author Frans Lundberg
 */
public class PerfTreeMapGet {
    
    @Nano("perf")
    public static void get(SimpleTestEnvironment r) {
        Random random = new Random(1);
        int n = 1000*1000;
        int m = 5;
        long t0, t1;
        Map<byte[], byte[]> map = new TreeMap<byte[], byte[]>(new ByteArrayComparator());
        
        byte[][] keys = new byte[n][];
        random = new Random(1);
        for (int i = 0; i < n; i++) {
            keys[i] = StringUtil.toBytes("" + random.nextInt());
        }
        
        for (int i = 0; i < n; i++) {
            map.put(keys[i], StringUtil.toBytes("v"));
        }
        
        t0 = System.nanoTime();
        for (int i0 = 0; i0 < m; i0++) {
            for (int i = 0; i < n; i++) {
                map.get(keys[i]);
            }
        }
        t1 = System.nanoTime();
        
        r.report("n", n);
        r.report("m", m);
        r.report("time-per-get", (t1-t0)*1e-9 / (m*n));
        r.report("total-time", (t1-t0)*1e-9);
    }
    
    public static void main(String[] args) throws Exception {
        get(new SimpleTestEnvironment());
    }
}

/*

2017-07-31
==========

New year, new computer, new JVM (OpenJDK 8, 64-bit), same test. Now only 0.4 us with n = 100*1000.
Updating to use 1M entries instead (and 5 repetitions), we have:

    $ j bergdb.test.java.PerfTreeMapGet
    * n: 1000000
    * m: 5
    * time-per-get: 9.858618662E-7
    * total-time: 4.929309331000001

When n = 1M, we get 0.95 us. Still less than 1 us for
one in a million.


2013-04-05
==========

$
* time-per-get: 2.5E-6

2012-03-08
==========

$ java -cp . -server com.bergdb.klong.PerfTreeMapGet
com.bergdb.klong.PerfTreeMapGet.get-n = 100000
com.bergdb.klong.PerfTreeMapGet.get-m = 10
com.bergdb.klong.PerfTreeMapGet.get-time = 3.11E-6
com.bergdb.klong.PerfTreeMapGet.get-total-time = 3.110907746
*/