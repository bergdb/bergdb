package bergdb.dag;

import static bergdb.nanotest.Assert.*;
import bergdb.nanotest.Nano;

/**
 * An spos (stream position) is a unique identifier for a stream item
 * in the DB stream. For performance reasons, an spos is stored as a long, not with a special class.
 * This class provides functionality for handling spos values.
 * A valid spos for a position in the state-stream is always non-negative.
 * 
 * @author Frans Lundberg
 */
abstract public class Spos {
    // Note, set NULL to -2 to test if used everywhere where it should be used.
    // But, consider on-disk, at-customer data.
    
    /**
     * Used to indicate "no spos", not considered a "valid" Spos.
     */
    public static final long NULL = -1;
    
    /** No instances needed. */
    private Spos() {}
    
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
        return spos >= 0 || spos == NULL;
    }
    
    public static final boolean isNull(long spos) {
        return spos == NULL;
    }
    
    
    // ======== Tests ========
    
    @Nano
    public static void testConstantCopy() {
        assertEquals(NULL, bergdb.storage.Constants.SposNULL);
    }
    
    @Nano
    public static void testIsNull() {
        assertTrue(isNull(NULL));
        assertFalse(isNull(12345));
    }
    
    @Nano
    public static void testIsValid() {
        assertTrue(isValid(1200));
        assertTrue(isValid(0));
        assertFalse(isValid(-1234));
        assertFalse(isValid(NULL));
    }
    
    @Nano
    public static void testIsValidOrNull() {
        assertTrue(isValidOrNull(1200));
        assertTrue(isValidOrNull(0));
        assertFalse(isValidOrNull(-1234));
        assertTrue(isValidOrNull(NULL));
    }
}
