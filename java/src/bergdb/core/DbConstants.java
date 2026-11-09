package bergdb.core;

import bergdb.common.Util;
import bergdb.dag.Constants;
import bergdb.dag.Keys;

/**
 * Constants for the database implementation.
 * 
 * @author Frans Lundberg
 */
public class DbConstants {

    /** 
     * IKP, Internal Key Prefix; prefix of keys used to store internal database data.
     * Keys with this prefix must not be used by an ordinary user.
     * The Pub Layer enforces this; the Core Layer does not (the rules: Db's Javadoc,
     * bergdb 020-22).
     * The string is an ikey (not ukey).
     */
    public static final String INTERNAL_PREFIX = Util.identity("/#i/");
    
    public static final long[] INTERNAL_PREFIX_SKEY = Keys.toSegments(INTERNAL_PREFIX);
    
    /** Used for internal dummy writes. */
    static final long[] DUMMY_KEY = Keys.toSegments(INTERNAL_PREFIX + "-dummy");
}
