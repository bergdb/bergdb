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
    // But, consider on-disk, at-user data.
    // Note 150515, index nodes have spos % 8 == 0. BUT, this is not
    // the case for value nodes. They can start at any mod8 value.
    //
    
    /**
     * Used to indicate "no spos", not considered a valid spos.
     */
    public static final long NULL = -1;
    
    /** No instances needed. */
    private Spos() {}
    
    /**
     * Returns true if the long is a valid stream position
     * (that is, a non-negative value).
     */
    public static final boolean isValid(long spos) {
        return spos >= 0;
    }
    
    public static final long nextVpos(long vpos) {
        // Next odd integer
        return vpos % 2 == 0 ? vpos + 1 : vpos + 2;
    }
    
    /**
     * @param spos  An spos of an index node.
     * @return true if the spos is a vpos (virtual spos).
     */
    public static final boolean isVpos(long spos) {
        return spos % 2 == 1;
    }
    
    /**
     * Returns true if spos is a valid stream position or NULL.
     */
    public static final boolean isValidOrNull(long spos) {
        return spos >= 0 || spos == NULL;
    }
    
    public static final boolean isNull(long spos) {
        return spos == NULL;
    }
    
    /**
     * Integer needed to add to 'a' so (a + result) % mod == 0.
     */
    public static final int addToAlign(int a, int mod) {
        return (mod - (a % mod)) % mod;
    }
    
    // ======== Tests ========
    
    @Nano
    private static void testAlign1() {
        assertEquals(0, addToAlign(0, 4));
        assertEquals(3, addToAlign(1, 4));
        assertEquals(2, addToAlign(2, 4));
        assertEquals(1, addToAlign(3, 4));
        assertEquals(0, addToAlign(4, 4));
        assertEquals(3, addToAlign(5, 4));
    }
    
    @Nano
    private static void testAlign2() {
        assertEquals(0, addToAlign(0, 3));
        assertEquals(2, addToAlign(1, 3));
        assertEquals(1, addToAlign(2, 3));
        assertEquals(0, addToAlign(3, 3));
        assertEquals(2, addToAlign(4, 3));
        assertEquals(1, addToAlign(5, 3));
    }
    
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
    
    @Nano
    public static void testNextVpos1() {
        assertEquals(1, Spos.nextVpos(0));
        assertEquals(5, Spos.nextVpos(3));
        assertEquals(11, Spos.nextVpos(9));
    }
    
    @Nano
    public static void testNextVpos2() {
        long vpos = 123456L;
        for (int i = 0; i < 40; i++) {
            long next = Spos.nextVpos(vpos);
            vpos++;
            
            if (next % 8 == 0) {
                throw new AssertionError("bad vpos, " + next);
            }
        }
    }
}
