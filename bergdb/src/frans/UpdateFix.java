package frans;

import bergdb.common.Util;
import bergdb.core.Db;
import bergdb.core.DbUtil;
import bergdb.core.KTestClock;
import bergdb.core.NoEvictBoss;
import bergdb.core.Trans;
import bergdb.graph.GetData;
import bergdb.graph.Graph;
import bergdb.graph.INode;
import bergdb.graph.KeyNode;
import bergdb.graph.Keys;
import bergdb.graph.TopNode;
import bergdb.graph.TransactionNodes;
import bergdb.nanotest.Assert;
import bergdb.nanotest.BasicCollector;
import bergdb.nanotest.TestCollector;
import bergdb.stream.MemoryStream;

/**
 * Trying to fix an issue detected 131016 on branch forward-pointers.
 * See test.BigDbWithDeletes.
 */
public class UpdateFix {
    
    String updateKey = "/k120";
    
    private void run2(TestCollector c) throws InterruptedException {
        int n = 250;
        int startupDistance = 10*1000;
        int valueSize = 1000;
        
        MemoryStream ms = new MemoryStream();
        KTestClock clock = new KTestClock();
        Db db = Db.builder().mainStream(ms).clock(clock).evictBoss(new NoEvictBoss())
                .startupDistance(startupDistance).start();
        
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
        
        clock.setTime(2*1000000);
        byte[] key1 = Keys.toBytes(updateKey);
        Trans t2 = Trans.builder().put(key1, new byte[123]).build();
        t2.listener = new Trans.Listener() {
            public void nodesWritten(TransactionNodes nodes) {
                for (int i = 0; i < nodes.size(); i++) {
                    INode n = nodes.get(i);
                    System.out.println("Trans node: " + n);
                }
            }
        };
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
        
        db.sync();
        db = null;
        c.out().println("db synced and set to null");
        
        ms = ms.copy();
        c.out().println("Memory stream copied.");
        
        clock.setTime(3*1000000);
        
        Db db2 = Db.builder().mainStream(ms).clock(clock).evictBoss(new NoEvictBoss()).build();
        long t = System.nanoTime();
        
        db2.start(new Db.StartListener() {
            public void tpos(long tpos) {
                //System.out.println("start() tpos: " + tpos);
            }
            
            public void startupDistance(long startupDistance) {
                System.out.println("start() startupDistance: " + startupDistance);
            }
            
            public void startPos(long startPos) {
                System.out.println("start() startPos: " + startPos);
            }
        });
        
        t = System.nanoTime() - t;
        clock.setTime(4*1000000);
        
        c.report("startup-time", 1e-9 * t);
        
        // Tests the restarted database (db2).
        
        this.printAccessPath(db2, "after restart");
        
        byte[] val = DbUtil.get(db2, Keys.toBytes(updateKey));
        if (val.length != 123) {
            throw new RuntimeException("Expected 123 long value, val.length=" 
                    + val.length);
        }
    }
    

    private void printAccessPath(Db db, String caseName) {
        String[] keys = new String[]{updateKey};
        
        GetData gd = db.newGetData();
        gd.pointerListener = new Graph.PointerListener() {
            public void superRootAccessed(TopNode superRoot) {
                System.out.println("Super root: " + superRoot);
            }
            
            public void pointerFollowed(INode predecessor, int pointerIndex, INode result, int pointerType) {
                System.out.println("Pointer followed, index " + pointerIndex + ", result: " + result);
                long id = result.getId();
                if (id == 242544L || id == 360720L) {
                    System.out.print(((KeyNode) result).print("    "));
                }
            }
        };
        
        System.out.println("\n---- " + caseName + ": Printing pointers ----");
        System.out.println("Stream length: " + db.getStreamLength());
        
        for (int i = 0; i < keys.length; i++) {
            String key = keys[i];
            System.out.println("* key: " + key);
            byte[] value = db.getOne(Long.MAX_VALUE, Keys.toSegments(key), gd);
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

131016. Minimized problem. Can reproduce with: 
  int n = 250;
  int startupDistance = 10*1000;
  int valueSize = 1000;
but not with n much smaller.

*/