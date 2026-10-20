package bergdb.common;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

public class HashUtil {


    /**
     * Returns an integer between 0 and upper-1 based
     * on hashing x.
     */
    public static final int mHashIndex(long x, int upper) {
        x = (x ^ (x >>> 30)) * 0xbf58476d1ce4e5b9L;
        x = (x ^ (x >> 27)) * 0x94d049bb133111ebL;
        x = x ^ (x >> 31);
        int r = (int) ((x ^ (x >>> 32)) & 0x7fffffff);
        return r % upper;
    }
    
    @Nano
    public static void testMHashIndex1() {
        long[] xValues = new long[]{0, 1, 1000, 1234567890123L, -100};
        int upper = 10000;
        
        for (long x : xValues) {
            int index = mHashIndex(x, upper);
            Assert.assertTrue(index >= 0);
            Assert.assertTrue(index < upper);
        }
    }
}
