import java.util.Map;

import bergdb.core.Db;
import bergdb.core.Trans;
import bergdb.stream.DummyStream;

/**
 * 005-08: MEM's database (as Probe006 histo, distance 50 MB), and the exact counts of
 * HashMap's bin objects that its million KVs add, from the class histogram.
 */
public class TreeCount {
    public static void main(String[] args) {
        int n = 1000 * 1000;
        Db db = Db.builder().testSetup().mainStream(new DummyStream()).startupDistance(50000000).start();
        Map<String, long[]> before = Probe006.histogram();
        for (int i = 0; i < n / 100; i++) {
            Trans.Builder b = db.trans();
            for (int j = 0; j < 100; j++) b.put("" + (i * 100 + j), new byte[0]);
            db.execute(b.build());
        }
        Map<String, long[]> after = Probe006.histogram();
        for (String c : new String[] {"java.util.HashMap$TreeNode", "java.util.HashMap$Node",
                "java.lang.Long", "bergdb.core.Cache3$CacheEntry"}) {
            long[] a = after.get(c), b = before.get(c);
            long objects = (a == null ? 0 : a[0]) - (b == null ? 0 : b[0]);
            long bytes = (a == null ? 0 : a[1]) - (b == null ? 0 : b[1]);
            System.out.println(c + ": " + objects + " objects, " + bytes + " bytes");
        }
        db.stop();
    }
}
