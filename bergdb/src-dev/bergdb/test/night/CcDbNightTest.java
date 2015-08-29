package bergdb.test.night;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.Random;

import bergdb.common.Bytes;
import bergdb.common.Util;
import bergdb.core.Cache2;
import bergdb.core.Db;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.Connection;
import bergdb.pub.CryptoKey;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.WBuilder;
import bergdb.pubimp.DatabaseImp;

/**
 * Up to 1M cards in a database. Lookup speed, disk size.
 * 
 * @author Frans Lundberg
 */
public class CcDbNightTest {
    //
    // 150818, copied original CcDbTest to here (bergdb.test.night) and adapted
    // for automatic testing (night test).
    // We have an cache evict related issue. If cache size increased enough,
    // the test is successful.
    //
    static final int MAX = 1 * 1000000;
    Database database;
    Connection c;
    int n;   // wanted number of cards
    String dir;
    boolean encrypt = true;
    int[] permutation;
    PrintStream out;
    Cache2.Evictor evictor;
    
    
    private void go() {
        computePermutation();
        
        createDb();
        
        addCards();
        
        Db db = ((DatabaseImp) database).getDb();
        evictor = Cache2.TestAccess.evictor(db.internal().cache());
        
        checkCount();
    }

    private void createDb() {
        if (dir == null) {
            dir = "./" + CcDbNightTest.class.getSimpleName();
        }
        
        CryptoKey key = CryptoKey.NULL;
        if (encrypt) {
            key = CryptoKey.parse(
                    "7bcf4b7c-salsa-15fc30dde0914feb075a2c1f1fb95640da3e3d04da10fe9c349ad99a50deaab4aa803d057a0186cc");
        }
        
        database = Factory.database()
                .dir(dir)
                .cryptoKey(key)
                .startupDistanceInMb(5)
                .targetCacheSizeInMb(50)
                .start();
        
        double time = database.getStartupInfo().getStartupDuration();
        out.format("Db started in %.2f seconds, dir:%s\n", time, dir);
        
        c = database.connection();
        initDb();
    }

    private void computePermutation() {
        permutation = new int[MAX];
        
        for (int i = 0; i < MAX; i++) {
            permutation[i] = i;
        }
        
        Random r = new Random(0);
        
        for (int i = 0; i < MAX; i++) {
            int index1 = i;
            int index2 = r.nextInt(MAX);
            
            int temp = permutation[index1];
            permutation[index1] = permutation[index2];
            permutation[index2] = temp;
        }
    }

    @SuppressWarnings("unused") 
    private void checkCount() {
        // Scan of /cards/ to count all cards.
        
        out.println("Counting all cards...");
        int counter = 0;
        
        long t0 = System.nanoTime();
        for (byte[] v : c.usePrimary(byte[].class).dir("/cards/").objects()) {
            counter++;
        }
        double time = 1e-9 * (System.nanoTime() - t0);
        
        out.format("Actual card count: %d. Counted in %.3f seconds (%.3f ms per card).\n", 
                counter, time, time / counter * 1000.0);
        out.format("evictCount: %d.\n", evictor.getEvictCount());
        
        if (counter != n) {
            throw new AssertionError("Missing cards, found " + counter + " cards out of " + n + ".");
        }
    }

    protected void finalize() {
        database.stop();
    }
    
    private void addCards() {
        final int existingCardCount = getCardCount();
        int toAdd = n - existingCardCount;
        
        toAdd = toAdd < 0 ? 0 : toAdd;
        out.println(toAdd + " cards to add.");
        if (toAdd == 0) {
            return;
        }
        
        int addedCounter = 0;
        
        long t0 = System.nanoTime();
        
        while (addedCounter < toAdd) {
            WBuilder b = c.w();
            
            for (int i = 0; i < 100; i++) {
                String key = cardIndexToKey(existingCardCount + addedCounter);
                b.put(key, new byte[100]);
                
                addedCounter++;
                if (addedCounter >= toAdd) {
                    break;
                }
            }
            
            b.put("/stats", new Stats(existingCardCount + addedCounter));
            b.execute();
            
            if (addedCounter % 10000 == 0) {
                out.println("Added " + addedCounter + " cards.");
            }
            
            if (addedCounter % 100000 == 0) {
                System.gc();
            }
        }
        
        double time = (System.nanoTime() - t0) * 1e-9;
        
        out.format("Added %d cards in %.1f s. %.3f ms per card.\n", 
                addedCounter, time, (time / addedCounter) * 1000.0);
        
        c.sync();
    }
    
    /** Database key string of a card with given index. */
    private String cardIndexToKey(int index) {
        if (index < 0 || index > n - 1) {
            throw new IllegalArgumentException("index=" + index);
        }
        
        return cardNumberToKey(permutation[index]);
    }
    
    /** Database key string of a card with given index. */
    private String cardNumberToKey(int cardNumberInt) {
        byte[] bytes = new byte[4];
        Bytes.intToBytesBE(cardNumberInt, bytes, 0);
        String key = "/cards/" + Util.toHex(bytes);
        return key;
    }
    
    private void initDb() {
        if (!c.exists("/stats")) {
            Stats s = new Stats();
            s.cards = 0;
            c.put("/stats", s);
        }
    }
    
    private int getCardCount() {
        return c.get("/stats", Stats.class).cards;
    }
    
    @Nano("night")
    private static void testIt(TestEnvironment env) throws IOException {
        File tempDir = env.createTempDir();
        
        CcDbNightTest t = new CcDbNightTest();
        t.dir = tempDir.getAbsolutePath();
        t.n = 400000;
        t.encrypt = false;
        t.out = env.out();
        
        t.go();
        
        env.out().println("Evict count: " + t.evictor.getEvictCount());
    }
    
    public static class Stats {
        int cards;   // estimated number of cards in database
        
        public Stats() {}
        
        public Stats(int cards) {
            this.cards = cards;
        }
    }
}

/*

150829
======

Added node evict condition [if (pointee.isDirty()) ]. Now this test works!
However, isDirty() is not thread-safe. The isDirty state of a node changes while putKv()
is executing.


150829
======

Reproducible error, now we get:
java.lang.AssertionError: Missing cards, found 399998 cards out of 400000.
Always the same amount of missing cards.

Before when Dag.appendKlongs() included code: [pd.nodeChangeListener.keyNodeCreated(last);]
we got:
    java.lang.AssertionError: Missing cards, found 399757 cards out of 400000.

So, it *does* matter.


150818 Issue
============

Frans: Detected this issue for the new cache code. Key nodes seem to be evicted when
they should not be. When increasing cache size, the issue disappears.

Tested to introduce spos limit, only nodes with spos < startupPos evict.
  --> No improvement.
  
Tested to call possiblyEvict() only from this class (not internally).
  --> No improvement.

Tested to add [... if (node.isDirty()) return;] to beginning of method 
Cache2.Evictor.evictNodePointers().
  --> Works!
  Yes, but this does not seem right.
  
Tested if statement:
    if (pointerAccessTime < accessTimeLimit && (pointee.isValueNode() || !node.isDirty())) {
        node.setPointer(i, null, pointeePos);
    }
  --> Works!

Problem seems to occur when 'node' is a dirty key node and pointee is a clean key node.
Why is that a problem?

*/