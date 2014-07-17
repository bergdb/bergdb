package bergdb.dag;

import bergdb.nanotest.Assert;
import bergdb.nanotest.T;

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
    
    private Spos() {}
    
    /**
     * Used to indicate "no spos".
     */
    public static final long NULL = -1;
    
    /**
     * Returns true if the long is a valid stream position (is non-negative).
     */
    public static final boolean isValid(long spos) {
        return spos >= 0;
    }
    
    /**
     * Returns true if spos is a valid stream position (is non-negative) or NULL.
     */
    public static final boolean isValidOrNull(long spos) {
        return isValid(spos) || spos == NULL;
    }
    
    
    // ======== Tests ========
    
    @T
    public static void testConstantCopy() {
        Assert.assertEquals(NULL, bergdb.storage.Constants.SposNULL);
    }
}
