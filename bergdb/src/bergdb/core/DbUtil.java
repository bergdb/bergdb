package bergdb.core;

import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.Locale;
import java.util.TimeZone;

import bergdb.common.Util;
import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.pub.Clock;


/**
 * Static utility methods related to DB.
 */
public class DbUtil {
    /**
     * Gets the first key in the database.
     * 
     * @param db  The database.
     * @param lookupTime  The DB time for which to make the lookup. Use Long.MAX_VALUE to 
     * lookup the state at the latest possible time.
     * @return Returns the first key, or null if no key exists at the given lookup time.
     * @throws IllegalStateException If start() has not been called.
     */
    public static byte[] getFirstKey(Db db, long lookupTime, GetData gd) {
        GetMany g = new GetMany();
        g.stopCondition = new GetMany.GetOne();
        g.startKey = null;
        g.lookupTime = lookupTime;
        db.getMany(g);
        
        byte[] result = null;
        if (g.result.size() > 0) {
            assert g.result.get(0) != null : "kvt null";
            assert g.result.get(0).key != null : "key null";
            result = Keys.toBytes(g.result.get(0).key);
        }
        return result;
    }

    public static byte[] get(Db db, long lookupTime, byte[] key) {
        assert db != null : "db == null not allowed";
        return db.getOne(lookupTime, Keys.toSegments(key), db.newGetData());
    }
    
    public static byte[] get(Db db, long lookupTime, String key) {
        assert db != null : "db == null not allowed";
        return db.getOne(lookupTime, Keys.toSegments(key), db.newGetData());
    }
    
    /**
     * Same as: <code>db.get(Long.MAX_VALUE, Klong.toSegments(key), new GetData());</code>.
     * 
     * @see Db#getOne(long, long[], GetData)
     */
    public static byte[] get(Db db, byte[] key) {
        return db.getOne(Long.MAX_VALUE, Keys.toSegments(key), db.newGetData());
    }
    
    public static byte[] get(Db db, String key) {
        return db.getOne(Long.MAX_VALUE, Keys.toSegments(key), db.newGetData());
    }
    
    public static String getString(Db db, String key) {
        byte[] value = db.getOne(Long.MAX_VALUE, Keys.toSegments(key), db.newGetData());
        return value == null ? null : Util.toString(value);
    }
    
    private static final SimpleDateFormat dateFormat;
    
    static { 
        dateFormat = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss.SSS", Locale.US);
        dateFormat.setTimeZone(TimeZone.getTimeZone("UTC"));
    }
    
    /**
     * Database time (long) to human-readable UTC time string.
     */
    public static String dbTimeToUtc(long dbTime) {
        long ms = dbTime / (Clock.UNITS_PER_SEC / 1000);
        return dateFormat.format(new Date(ms)) + " UTC";
    }
    
    private static long unity(long value) {
        return value;
    }
    
    public static void main(String[] args) {
        assert unity(Clock.UNITS_PER_SEC) % 1000 == 0;
            // unity() used to avoid warning.
        System.out.println(dbTimeToUtc(System.currentTimeMillis() * (Clock.UNITS_PER_SEC / 1000)));
    }
}
