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
    
    /**
     * The startup distance's key, "/#i/-startup-distance" (bergdb 028-15): its value, the
     * setting in force, is 4 bytes, an int, little-endian, from 10 to 10^9
     * (DbBuilder.MAX_STARTUP_DISTANCE). Written by the creating start and by
     * Db.setStartupDistance(), read at the end of a start (Db.readStartupDistanceKv). Until
     * the meta block's version 155, the setting was the meta block's, bytes 40 to 43, and
     * setStartupDistance() put 200,000 zero bytes at "/#i/-dummy" to get a meta block written.
     */
    static final long[] SD_KEY = Keys.toSegments(INTERNAL_PREFIX + "-startup-distance");
}
