package bergdb.core;

import java.util.zip.CRC32;
import java.util.zip.Checksum;

import bergdb.common.Bytes;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.stream.MemoryStream;

/**
 * Utility to scan a database collecting statistics and computing checksums
 * while doing so.
 * Do not reuse instance of this class for multiple scans.
 * 
 * @author Frans Lundberg
 */
public class DbScan {
    private Db db;
    private boolean includeInternal = false;
    private boolean includeKvTime = false;
    private long[] from = null;
    private long[] to = null;
    private long lookupTime = Long.MAX_VALUE;
    
    public DbScan(Db db) {
        this.db = db;
    }
    
    public DbScan includeInternal(boolean b) {
        this.includeInternal = b;
        return this;
    }
    
    public DbScan includeKvTime(boolean b) {
        this.includeKvTime = b;
        return this;
    }
    
    public DbScan lookupTime(long lookupTime) {
        this.lookupTime = lookupTime;
        return this;
    }
    
    public Result scan() {
        // This method uses a special StopCondition.
        // No Kvs are added to a result.
        
        final Checksum sum = new CRC32();
        final Result result = new Result();
        
        GetMany.StopCondition condition = new GetMany.StopCondition() {
            public int handleKvt(Kvt kvt) {
                
                if (to != null && Keys.compareKeys(kvt.key, to) >= 0) {
                    return GetMany.StopCondition.STOP;
                }
                
                if (!includeInternal) {
                    boolean isInternal = Keys.isPrefix(DbConstants.INTERNAL_PREFIX_SKEY, kvt.key);
                    if (isInternal) {
                        return GetMany.StopCondition.CONTINUE;
                    }
                }
                
                byte[] bkey = Keys.toBytes(kvt.key);
                byte[] value = kvt.value;
                
                sum.update(bkey, 0, bkey.length);
                sum.update(value, 0, value.length);
                
                if (includeKvTime) {
                    byte[] timeBytes = new byte[8];
                    Bytes.longToBytesLE(kvt.time, timeBytes, 0);
                    sum.update(timeBytes, 0, timeBytes.length);
                }
                
                result.kvCount++;
                
                return GetMany.StopCondition.CONTINUE;
            }
            
            public void eod() {
                // empty
            }
        };
        

        GetMany g = db.newGetMany();
        g.lookupTime = lookupTime;
        g.stopCondition = condition;
        g.startKey = from;
        db.getMany(g);
        
        assert g.result != null : "g.result == null";
        assert g.result.size() == 0 : "unexpected, " + g.result.size();
        
        result.checksum = sum.getValue();
        return result;
    }
    
    public static class Result {
        public long checksum;
        public long kvCount;
    }
    
    
    
    // ======== Test ========
    
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
    
    @Nano private static void testThatItMatchesDbUtilChecksum() {
        Db db = createEmptyDb();
        db.execute(db.trans().put("/key1", "v1"));
        db.execute(db.trans().put("/key2", "v2"));
        long c1 = DbUtil.checksum(db);
        
        DbScan scan = new DbScan(db);
        DbScan.Result r = scan.scan();
        
        Assert.assertEquals(c1, r.checksum);
    }
    
    @Nano private static void checkKvCount() {
        Db db = createEmptyDb();
        db.execute(db.trans().put("/key1", "v1"));
        db.execute(db.trans().put("/key2", "v2"));
        
        DbScan scan = new DbScan(db);
        DbScan.Result r = scan.scan();
        
        Assert.assertEquals(2, r.kvCount);
    }
}
