package bergdb.test.manual;

import java.io.IOException;
import java.util.Random;

import bergdb.common.Bytes;
import bergdb.common.StringUtil;
import bergdb.nanotest.CommandLine;
import bergdb.pub.Connection;
import bergdb.pub.CryptoKey;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.WBuilder;

/**
 * Up to 1M cards in a database. Lookup speed, disk size.
 * 
 * @author Frans Lundberg
 */
public class CcDbTest {
    //
    // Frans: naming inspired by ASSAABLOY CC project.
    //
    static final int MAX = 1 * 1000000;
    Database database;
    Connection c;
    int n = 100*1000;   // wanted number of cards
    String dir;
    CommandLine commandLine;
    boolean encrypt = true;
    int[] permutation;
    boolean waitForEnter = false;
    
    private void go(String[] args) {
        System.out.println("==== " + CcDbTest.class.getName() + " ====");
        
        commandLine = new CommandLine(args);
        
        if (commandLine.has("help")) {
            StringBuilder b = new StringBuilder();
            b.append("Help for " + CcDbTest.class.getSimpleName() + ". Options:\n");
            b.append("-n  Number of cards to simulate (default = 100000)\n");
            b.append("-dir  Database data directory (default = CcDbTest).\n");
            b.append("-noEncrypt  Don't encrypt database (encrypted by default).\n");
            b.append("-press  Pause till ENTER pressed while adding cards.\n");
            
            System.out.println(b.toString());
            return;
        }
        
        if (commandLine.hasOne("n")) {
            n = Integer.parseInt(commandLine.getOne("n"));
        }
        
        if (commandLine.hasOne("dir")) {
            dir = commandLine.getOne("dir");
        }
        
        if (commandLine.has("noEncrypt")) {
            encrypt = false;
        }
        
        waitForEnter = commandLine.has("press");
        
        
        if (n > MAX) {
            System.out.println("n too large, MAX = " + MAX + ".");
            return;
        }
        
        System.out.println("Card count (n): " + n);
        
        
        computePermutation();
        
        createDb();
        
        try {
            addCardsIfNeeded();
            
            measurePerformance();
            
            count();
        } finally {
            database.stop();
        }
    }

    private void createDb() {
        if (dir == null) {
            dir = "./" + CcDbTest.class.getSimpleName();
        }
        
        CryptoKey key = CryptoKey.NULL;
        if (encrypt) {
            key = CryptoKey.parse(
                    "7bcf4b7c-salsa-15fc30dde0914feb075a2c1f1fb95640da3e3d04da10fe9c349ad99a50deaab4aa803d057a0186cc");
        }
        
        database = Factory.database()
                .create(dir)
                .cryptoKey(key)
                .startupDistanceInMb(5)
                .start();
        
        double time = database.getStartupInfo().getStartupDuration();
        System.out.format("Db started in %.2f seconds, dir:%s\n", time, dir);
        
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
    private void count() {
        // Scan of /cards/ to count all cards.
        
        System.out.println("Counting all cards...");
        int counter = 0;
        
        long t0 = System.nanoTime();
        for (byte[] v : c.usePrimary(byte[].class).dir("/cards/").objects()) {
            counter++;
        }
        double time = 1e-9 * (System.nanoTime() - t0);
        
        System.out.format("Actual card count: %d. Counted in %.3f seconds (%.3f ms per card).\n", 
                counter, time, time / counter * 1000.0);
    }

    private void addCardsIfNeeded() {
        final int existingCardCount = getCardCount();
        int toAdd = n - existingCardCount;
        
        toAdd = toAdd < 0 ? 0 : toAdd;
        System.out.println(toAdd + " cards to add.");
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
                System.out.println("Added " + addedCounter + " cards.");
                if (commandLine.has("press")) {
                    waitForEnter();
                }
            }
        }
        
        double time = (System.nanoTime() - t0) * 1e-9;
        
        System.out.format("Added %d cards in %.1f s. %.3f ms per card.\n", 
                addedCounter, time, (time / addedCounter) * 1000.0);
        c.sync();
    }
    
    private void waitForEnter() {
        System.out.print("Press ENTER to continue...");
        try {
            System.in.read();
        } catch (IOException e) {
            // empty
        }
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
        String key = "/cards/" + StringUtil.toHex(bytes);
        return key;
    }

    private void measurePerformance() {
        Random random = new Random(0);
        int count = 10*1000;
        int missing = 0;
        
        long t0 = System.nanoTime();
        for (int i = 0; i < count; i++) {
            int cardIndex = random.nextInt(n);
            String key = cardIndexToKey(cardIndex);
            byte[] value = c.get(key, byte[].class);
            if (value == null) {
                String message = "Missing card data, key: " 
                        + key + ", cardIndex: " + cardIndex + ", permutation: " + permutation[cardIndex];
                //throw new IllegalStateException(message);
                
                missing++;
                System.out.println(message);
            }
        }
        
        double time = (System.nanoTime() - t0) * 1e-9;
        double timePerLookup = time / count;
        
        if (missing > 0) {
            System.out.println("Missing " + missing + " cards.");
        }
        
        System.out.format("Lookup of %d cards in %.3f s, per lookup: %.3f ms.\n", count, time, timePerLookup * 1000.0);
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

    public static void main(String[] args) {
        new CcDbTest().go(args);
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

150731 Frans:
Class in BergDB project created based on tests in CC project.

150622 Frans: On a10.
Card count, lookup time. 10k cards out of total, random access.
100k        0.2 ms
400k        0.5 ms
1000k       0.9 ms

150427 Frans:
On a10, 100k cards. Added 100k cards, in 40 s.
Lookup time: 0.2 ms per card. 10k out of 100k.

*/