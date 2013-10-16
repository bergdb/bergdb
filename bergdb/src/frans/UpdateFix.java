package frans;

import bergdb.common.Util;
import bergdb.core.Db;
import bergdb.core.DbUtil;
import bergdb.core.KTestClock;
import bergdb.core.KeyFactory;
import bergdb.core.NoEvictBoss;
import bergdb.core.Trans;
import bergdb.coreds.GetData;
import bergdb.coreds.Graph;
import bergdb.coreds.INode;
import bergdb.coreds.KeyNode;
import bergdb.coreds.Keys;
import bergdb.coreds.TopNode;
import bergdb.nanotest.Assert;
import bergdb.nanotest.BasicCollector;
import bergdb.nanotest.TestCollector;
import bergdb.pub.Database;
import bergdb.pubimp.DatabaseImp;
import bergdb.pubimp.PubKeys;
import bergdb.stream.MemoryStream;

/**
 * Trying to fix an issue detected 131016 on branch forward-pointers.
 * See test.BigDbWithDeletes.
 */
public class UpdateFix {
    
    private void run2(TestCollector c) throws InterruptedException {
        int n = 1000;
        MemoryStream ms = new MemoryStream();
        KTestClock clock = new KTestClock();
        Db db = Db.builder().mainStream(ms).clock(clock).evictBoss(new NoEvictBoss())
                .startupDistance(1*1000000).start();
        final int valueSize = 2000;
        
        c.report("kv-count", n);
        
        for (int i = 0; i < n; i++) {
            clock.setTime(1*1000000 + i);
            byte[] key = Keys.toBytes("/k" + i);
            byte[] value = new byte[valueSize];
            value[0] = (byte) Util.toString(key).hashCode();
            Trans t = Trans.builder().put(key, value).build();
            db.execute(t);
        }
        
        this.printAccessPath(db, "before update");
        
        // Updates one value
        
        clock.setTime(2*1000000 + 120);
        byte[] key1 = Keys.toBytes("/k120");
        Trans t2 = Trans.builder().put(key1, new byte[123]).build();
        db.execute(t2);
        
        // Tests database after update.
        
        this.printAccessPath(db, "after update");
        System.out.println("Stream length: " + db.getStreamLength());
        
        
        byte[] expectedValue = new byte[valueSize];
        
        for (int i = 0; i < n; i++) {
            byte[] key = Keys.toBytes("/k" + i);
            byte[] value = DbUtil.get(db, Long.MAX_VALUE, key);
            
            if (i == 120) {
                Assert.assertEquals(123, value.length);
            } else {
                if (value == null) {
                    throw new RuntimeException("value == null, i = " + i + ".");
                }
                
                expectedValue[0] = (byte) Util.toString(key).hashCode();
                Assert.assertEquals("i=" + i, expectedValue[0], value[0]);
            }
        }
        
        db = null;
        c.out().println("db set to null");
        
        clock.setTime(3*1000000);
        
        Db db2 = Db.builder().mainStream(ms).clock(clock).evictBoss(new NoEvictBoss()).build();
        long t = System.nanoTime();
        db2.start();
        t = System.nanoTime() - t;
        clock.setTime(4*1000000);
        
        c.report("startup-time", 1e-9 * t);
        
        // Tests the restarted database (db2).
        
        this.printAccessPath(db2, "after restart");
        
        byte[] val = DbUtil.get(db2, Keys.toBytes("/k120"));
        if (val.length != 123) {
            throw new RuntimeException("Expected 123 long value, val.length=" 
                    + val.length);
        }
    }
    

    private void printAccessPath(Db db, String caseName) {
        String[] keys = new String[]{"/k120"};
        
        GetData gd = db.newGetData();
        gd.pointerListener = new Graph.PointerListener() {
            public void superRootAccessed(TopNode superRoot) {
                System.out.println("Super root: " + superRoot);
            }
            
            public void pointerFollowed(INode predecessor, int pointerIndex, INode result, int pointerType) {
                System.out.println("Pointer followed, index " + pointerIndex + ", result: " + result);
                long id = result.getId();
                if (id == 318992L || id == 469640L) {
                    System.out.print(((KeyNode) result).print("    "));
                }
            }
        };
        
        System.out.println("\n---- " + caseName + ": Printing pointers ----");
        System.out.println("Stream length: " + db.getStreamLength());
        
        for (int i = 0; i < keys.length; i++) {
            String key = keys[i];
            System.out.println("* key: " + key);
            byte[] value = db.getOne(Long.MAX_VALUE, Keys.toSegments("/k120"), gd);
            System.out.println("value = " + value);
        }
        
        //dbTemp.getOne(Long.MAX_VALUE, Keys.toSegments(), gd);
        //dbTemp.getOne(Long.MAX_VALUE, Keys.toSegments(accountKey(999000)), gd);
        System.out.println("Print done.");
        
    }
    
    public static void main(String[] args) throws InterruptedException {
        TestCollector c = new BasicCollector();
        new UpdateFix().run2(c);
    }
}

/*
    
Same issue with both delete and update of value.

*/