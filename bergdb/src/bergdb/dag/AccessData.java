package bergdb.dag;

import bergdb.nanotest.Assert;
import bergdb.nanotest.T;

/**
 * <p>This class provides some functionality and most importantly documentation for node 
 * "access data". The access data is stored as a long for performance reasons, not as a special 
 * class. In addition, the access data long value shares storage space with an spos 
 * (stream position) in KeyNode.pos (long[]) field. 
 * An spos is used when we have a stream pointer, access data is
 * used when we have a memory pointer. There is no need to have access data information for
 * a stream pointer, so we can share the storage as an optimization.</p>
 * 
 * <p>The access data is updated when the pointer in a TopNode or KeyNode is followed.
 * The value is used by the cache eviction to know when to evict a node from the cache.</p>
 * 
 * <p>An access data long should be created only with method Db.getAccessData().
 * The current implementation of the method returns a value based on the counter 
 * DB.cachedMemoryValue.</p>
 * 
 * <p>The value of an access data long is always negative, LTE -10 (LTE DB.MIN_CACHE_MEMORY_VALUE).
 * The negative range is used to differentiate it from an spos that is always non-negative.</p>
 * 
 * @see Spos
 * @see KeyNode#pos
 */
public class AccessData {
    
    private AccessData() {}
    
    /**
     * Can be used when access data is unknown or unimportant. For testing, for example.
     * The value is considered a valid accessData value and will pass asserts.
     */
    public static final long DEFAULT_ACCESS_DATA = -10;
    
    /**
     * Checks whether the access data (a long) is valid.
     */
    public static final boolean isValid(long accessData) {
        return accessData <= -Constants.MIN_CACHE_MEMORY_VALUE;
    }
    
    public static final boolean isValidOrNull(long accessData) {
        return isValid(accessData) || accessData == Spos.NULL;
    }
    
    /**
     * Returns "access time", given an access data long.
     */
    public static final long getAccessTime(long accessData) {
        long result = -accessData;
        assert result >= Constants.MIN_CACHE_MEMORY_VALUE : "Unexpected accessData, " + accessData;
        return result;
    }
    
    /**
     * Returns "access time", given an access data long.
     */
    public static final long getAccessTimeNoChecks(long accessData) {
        return -accessData;
    }
    
    
    // ======== Tests ========
    
    @T
    public static void test1() {
        long accessData = -Constants.MIN_CACHE_MEMORY_VALUE;
        Assert.assertTrue(isValid(accessData));
    }
}
