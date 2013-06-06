package kissdb.core;

import kissdb.nanotest.Assert;
import kissdb.nanotest.T;

public class RerunException extends RuntimeException {
    private static final long serialVersionUID = 1L;
    
    private long keyHash;
    
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
