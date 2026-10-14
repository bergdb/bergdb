package bergdb.common;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * Immutable 2-tuple implementation.
 * This class and Triplet forms a very simple tuple library for BergDB. 
 * If we need more, we could switch to http://www.javatuples.org/.
 * 
 * @see Triplet
 * @author Frans Lundberg
 */
public class Pair<T0, T1> {
    private final T0 v0;
    private final T1 v1;
    
    public Pair(T0 v0, T1 v1) {
        this.v0 = v0;
        this.v1 = v1;
    }
    
    public final T0 value0() {
        return v0;
    }
    
    public final T1 value1() {
        return v1;
    }
    
    @Nano
    public static void test0() {
        Pair<String, Long> score = new Pair<String, Long>("teamA", 22L);
        Assert.assertEquals("teamA", score.value0());
        Assert.assertEquals(22L, (long) score.value1());
    }
}
