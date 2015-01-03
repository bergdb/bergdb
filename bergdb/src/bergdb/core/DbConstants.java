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
     * Keys with this prefix must not be used by a user directly.
     * The Pub Layer enforces this; the Core Layer does not.
     */
    public static final String INTERNAL_KEY_PREFIX = Util.identity("/#i/");
    
    /** Minimum possible cacheMemoryValue. */
    public static final long MIN_CACHE_MEMORY_VALUE = Constants.MIN_CACHE_MEMORY_VALUE;
    
    /** Used for internal dummy writes. */
    static final long[] DUMMY_KEY = Keys.toSegments(INTERNAL_KEY_PREFIX + "-dummy");
}
