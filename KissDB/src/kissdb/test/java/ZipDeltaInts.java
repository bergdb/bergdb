package kissdb.test.java;

import java.util.Random;

/**
 * ZIP performance, compression of consecutive longs with a random
 * difference of 1 to 10.
 * 
 * @author Frans Lundberg
 */
public class ZipDeltaInts extends Zip {
    public long[] createInts(int n) {
        Random random = new Random(0);
        long[] ints = new long[n];
        ints[0] = random.nextLong();
        for (int i = 1; i < n; i++) {
            ints[i] = ints[i-1] + (int) (10.0 * random.nextDouble()) + 1;
        }
        return ints;
    }
}
