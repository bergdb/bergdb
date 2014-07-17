package bergdb.core;

import bergdb.nanotest.Assert;
import bergdb.nanotest.T;

public class RerunException extends RuntimeException {
    private static final long serialVersionUID = 1L;
    private final long keyHash;
    
    public RerunException(long keyHash) {
        this.keyHash = keyHash;
    }
    
    public long getKeyHash() {
        return keyHash;
    }
    
    @T
    public static void test1() {
        Assert.assertEquals(1234L, new RerunException(1234L).getKeyHash());
    }
}
