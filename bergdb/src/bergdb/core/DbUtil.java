package bergdb.core;

import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.Locale;
import java.util.TimeZone;
import java.util.zip.CRC32;
import java.util.zip.Checksum;

import bergdb.common.Bytes;
import bergdb.common.Util;
import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
import bergdb.pub.Clock;
import bergdb.stream.MemoryStream;


/**
 * Static utility methods related to Db; Db help functions.
 * Useful for a Core Layer user.
 * 
 * @author Frans Lundberg
 */
public class DbUtil {
    
    private DbUtil() {}
    
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
        GetMany g = db.newGetMany();
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
    
    private static final SimpleDateFormat DATE_FORMAT;
    
    static { 
        DATE_FORMAT = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss.SSS", Locale.US);
        DATE_FORMAT.setTimeZone(TimeZone.getTimeZone("UTC"));
    }
    
    /**
     * Database time (long) to human-readable UTC time string.
     */
    public static String dbTimeToUtc(long dbTime) {
        long ms = dbTime / (Clock.UNITS_PER_SEC / 1000);
        return DATE_FORMAT.format(new Date(ms)) + " UTC";
    }
    
    /**
     * Computes a CRC32 checksum of the state of the database. All KVs are included, 
     * also internal KVs. Time of Kvs are optionally included.
     * 
     * @param dbTime  Lookup time to use.
     * @param includeKvTime  If true, the database write time of each KV is included in the result.
     * @return The checksum.
     */
    public static long checksum(Db db, final long dbTime, final boolean includeKvTime) {
        // This method uses a special StopCondition to compute the checksum.
        // No Kvs are added to the result.
        
        final Checksum sum = new CRC32();
        
        GetMany.StopCondition condition = new GetMany.StopCondition() {
            public int handleKvt(Kvt kvt) {
                byte[] bkey = Keys.toBytes(kvt.key);
                byte[] value = kvt.value;
                
                sum.update(bkey, 0, bkey.length);
                sum.update(value, 0, value.length);
                
                if (includeKvTime) {
                    byte[] timeBytes = new byte[8];
                    Bytes.longToBytesLE(kvt.time, timeBytes, 0);
                    sum.update(timeBytes, 0, timeBytes.length);
                }
                
                return GetMany.StopCondition.CONTINUE;
            }
            
            public void eod() {
                // empty
            }
        };
        

        GetMany g = db.newGetMany();
        g.lookupTime = dbTime;
        g.stopCondition = condition;
        g.startKey = null;
        db.getMany(g);
        
        assert g.result != null : "g.result == null";
        assert g.result.size() == 0 : "unexpected, " + g.result.size();
        
        return sum.getValue();
    }
    
    
    // ======== Testing ========
    
    private static Db createEmptyDb() {
        return createEmptyDb(100);
    }
    
    private static Db createEmptyDb(long firstTime) {
        TestClock clock = new TestClock();
        clock.setTime(firstTime);
        MemoryStream stream = new MemoryStream();
        Db db = Db.builder().clock(clock).stream("main", stream).build();
        db.start();
        return db;
    }
    
    @T
    private static void testChecksumForEmptyDb() {
        Db db1 = createEmptyDb();
        Db db2 = createEmptyDb();
        
        long t = Long.MAX_VALUE;
        long c1 = DbUtil.checksum(db1, t, true);
        long c2 = DbUtil.checksum(db2, t, true);
        
        Assert.assertEquals(c1, c2);
    }
    
    @T
    private static void testChecksumForOneKv1() {
        Db db1 = createEmptyDb();
        Db db2 = createEmptyDb();
        
        db1.execute(Trans.builder().put("/key1", "v1"));
        db2.execute(Trans.builder().put("/key1", "v1"));
        
        long t = Long.MAX_VALUE;
        long c1 = DbUtil.checksum(db1, t, true);
        long c2 = DbUtil.checksum(db2, t, true);
        
        Assert.assertEquals(c1, c2);
    }
    
    @T
    private static void testChecksumForDiffInValue() {
        Db db1 = createEmptyDb();
        Db db2 = createEmptyDb();
        
        db1.execute(Trans.builder().put("/key1", "v1"));
        db2.execute(Trans.builder().put("/key1", "v2"));   // <-- diff in value
        
        long t = Long.MAX_VALUE;
        long c1 = DbUtil.checksum(db1, t, true);
        long c2 = DbUtil.checksum(db2, t, true);
        
        Assert.assertTrue(c1 != c2);
    }
    
    @T
    private static void testChecksumForDiffInKey() {
        Db db1 = createEmptyDb();
        Db db2 = createEmptyDb();
        
        db1.execute(Trans.builder().put("/key1", "v1"));
        db2.execute(Trans.builder().put("/key2", "v1"));   // <-- diff in key
        
        long t = Long.MAX_VALUE;
        long c1 = DbUtil.checksum(db1, t, true);
        long c2 = DbUtil.checksum(db2, t, true);
        
        Assert.assertTrue(c1 != c2);
    }
    
    @T
    private static void testChecksumForDiffInTime1() {
        Db db1 = createEmptyDb(100);
        Db db2 = createEmptyDb(200);
        
        db1.execute(Trans.builder().put("/key1", "v1"));
        db2.execute(Trans.builder().put("/key1", "v1"));
        
        long t = Long.MAX_VALUE;
        long c1 = DbUtil.checksum(db1, t, true);
        long c2 = DbUtil.checksum(db2, t, true);
        
        Assert.assertTrue(c1 != c2);
    }
    
    @T
    private static void testChecksumForDiffInTime2() {
        // Test with parameter includeKvTime == false, time should not be included in checksum.
        
        Db db1 = createEmptyDb(100);
        Db db2 = createEmptyDb(200);
        
        db1.execute(Trans.builder().put("/key1", "v1"));
        db2.execute(Trans.builder().put("/key1", "v1"));
        
        long t = Long.MAX_VALUE;
        long c1 = DbUtil.checksum(db1, t, false);
        long c2 = DbUtil.checksum(db2, t, false);
        
        Assert.assertTrue(c1 == c2);
    }
    
    @T
    private static void testChecksumWithMultipleKvs() {
        Db db1 = createEmptyDb();
        Db db2 = createEmptyDb();
        db1.execute(Trans.builder().put("/key1", "v1"));
        db1.execute(Trans.builder().put("/key2", "v2"));
        db2.execute(Trans.builder().put("/key1", "v1"));
        db2.execute(Trans.builder().put("/key2", "v2"));
        
        long t = Long.MAX_VALUE;
        long c1 = DbUtil.checksum(db1, t, true);
        long c2 = DbUtil.checksum(db2, t, true);
        
        Assert.assertTrue(c1 == c2);
    }
}
