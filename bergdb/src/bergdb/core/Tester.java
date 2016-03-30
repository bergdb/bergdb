package bergdb.core;

import static bergdb.nanotest.Assert.assertEquals;
import bergdb.nanotest.Nano;

/**
 * General tests for the package.
 * 
 * @author Frans Lundberg
 */
public class Tester {
    
    @Nano
    public static void testSposNullCopy() {
        assertEquals(bergdb.dag.Spos.NULL, bergdb.storage.Constants.SposNULL);
    }
}
