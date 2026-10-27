package bergdb.storage;

import bergdb.common.Util;

/**
 * Constants for this package.
 * 
 * @author Frans Lundberg
 */
public class Constants {    
    private Constants() {}
    
    /**
     * Equals bergdb.dag.Spos.NULL.
     * Needed to avoid disallowed package dependency.
     */
    public static final int SposNULL = Util.identity(-1);
}
