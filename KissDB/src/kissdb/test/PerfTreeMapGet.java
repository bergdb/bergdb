package kissdb.test;

import java.util.Map;
import java.util.Random;
import java.util.TreeMap;

import kissdb.common.ByteArrayComparator;
import kissdb.common.Util;
import kissdb.nanotest.BasicCollector;
import kissdb.nanotest.T;


/**
 * Performance for get from TreeMap.
 */
public class PerfTreeMapGet {
    @T("perf")
    public static void get(BasicCollector r) {
        Random random = new Random(1);
        int n = 100*1000;
        int m = 10;
        long t0, t1;
        Map<byte[], byte[]> map = new TreeMap<byte[], byte[]>(new ByteArrayComparator());
        
        byte[][] keys = new byte[n][];
        random = new Random(1);
        for (int i = 0; i < n; i++) {
            keys[i] = Util.toBytes("" + random.nextInt());
        }
        
        for (int i = 0; i < n; i++) {
            map.put(keys[i], Util.toBytes("v"));
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
        get(new BasicCollector());
    }
}

/*

2013-04-05
$
* time-per-get: 2.5E-6

2012-03-08
$ java -cp . -server com.kissdb.klong.PerfTreeMapGet
com.kissdb.klong.PerfTreeMapGet.get-n = 100000
com.kissdb.klong.PerfTreeMapGet.get-m = 10
com.kissdb.klong.PerfTreeMapGet.get-time = 3.110907746E-6
com.kissdb.klong.PerfTreeMapGet.get-total-time = 3.110907746
*/