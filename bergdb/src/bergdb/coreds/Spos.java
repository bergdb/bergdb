package bergdb.coreds;

import bergdb.core.Db;
import bergdb.nanotest.Assert;

/**
 * An spos (stream position) is a unique identifier for a stream item
 * in the DB stream. For performance reasons, an spos is stored as a long, not in a special class.
 * This class provides functionality for handling spos values.
 * A valid spos for a position in the state-stream is always non-negative.
 * 
 * @author Frans Lundberg
 */
abstract public class Spos {
    // Note, set NULL to -2 to test if used everywhere where it should be used.
    
    /**
     * Used to indicate "no spos".
     */
    public static final long NULL = -1;
    
    /**
     * Can be used when access data is unknown or unimportant. For testing, for example.
     * The value is considered a valid accessData value and will pass asserts.
     */
    public static final long DEFAULT_ACCESS_DATA = -Db.MIN_CACHE_MEMORY_VALUE;
    
    /** Dummy test method to mark class as "tested". */
    public static void test1() {
        new Spos() {};
    }
    
    public static void testConstantCopy() {
        Assert.assertEquals(NULL, bergdb.storage.Constants.SposNULL);
    }
}
