package bergdb.test.manual;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Random;

import bergdb.common.Bytes;
import bergdb.common.Util;
import bergdb.core.Db;
import bergdb.core.Evictor;
import bergdb.core.FixedDurationEvictBoss;
import bergdb.dag.EvictData;
import bergdb.nanotest.CommandLine;
import bergdb.pub.Connection;
import bergdb.pub.CryptoKey;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.WBuilder;
import bergdb.pubimp.DatabaseBuilderImp;
import bergdb.pubimp.DatabaseImp;
import bergdb.test.manual.CcDbTest.Stats;

/**
 * Executable class with interactive database testing. 
 * Starts a database which is then controlled from command-line.
 * Suitable to use together with jvisualvm for example.
 * Developed with a focus on testing node cache / cache eviction.
 * 
 * @author Frans Lundberg
 */
public class Interactive {
    private String dirname = "Interactive-db";
    private CryptoKey cryptoKey = CryptoKey.NULL;
    private Database database;
    private Db db;
    private BufferedReader reader;
    int[] permutation = null;   // card permutation
    static final int MAX = 1 * 1000000;
    private Connection c;
    int n = 100*1000;   // wanted number of cards
    
    private void go(String[] args) throws Exception {
        CommandLine line = new CommandLine(args);
        
        handleCommandLine(line);
        start();
        runInteractively();
    }
    
    private void runInteractively() throws IOException {
        reader = new BufferedReader(new InputStreamReader(System.in, "UTF-8"));
        
        while (true) {
            System.out.println("Enter command: ");
            String line = reader.readLine().trim();
            String[] args = line.split(" ");
            if (args.length == 0) {
                continue;
            }
            
            String commandName = args[0];
            CommandLine options = new CommandLine(args);
            
            boolean exit = runCommand(commandName, options);
            if (exit) {
                break;
            }
        }
    }

    private boolean runCommand(String commandName, CommandLine options) {
        boolean shouldExit = false;
        
        if (commandName.equals("help")) {
            System.out.println("Help...");
        } else if (commandName.equals("addCards")) {
            runAddCards(options);
        } else if(commandName.equals("exit")) {
            shouldExit = true;
        } else if(commandName.equals("info")) {
            runInfo(options);
        } else if(commandName.equals("gc")) {
            runGc(options);
        } else if(commandName.equals("evict")) {
            runEvict(options);
        } else {
            System.out.println("Unknown command.");
        }
        
        return shouldExit;
    }

    private void runEvict(CommandLine options) {
        EvictData ed = new EvictData();
        int count = 1000;
        
        if (options.hasOne("n")) {
            count = Integer.parseInt(options.getOne("n"));
        }
        
        Evictor evictor = db.internal().evictor();
        long totalEvictCount = 0;
        long totalPointerCount = 0;
        
        long totalReasonAccessTime = 0;
        long totalReasonDirty = 0;
        long totalReasonNotMem = 0;
        
        long t0 = System.nanoTime();
        
        for (int i = 0; i < count; i++) {
            evictor.evict(ed);
            totalEvictCount += ed.evictCount;
            totalPointerCount += ed.totalCount;
            
            totalReasonAccessTime += ed.reasonAccessTime;
            totalReasonDirty += ed.reasonDirty;
            totalReasonNotMem += ed.reasonNotMem;
        }
        
        double time = 1e-9 * (System.nanoTime() - t0);
        
        System.out.format("count:%d, evicted: %d (of %d)\n", count, totalEvictCount, totalPointerCount);
        System.out.format("time per evict call: %.1f us.\n", 1e6 * (time / count));
        System.out.format("startupPos: %.1f | %.1f, stream length: %.1f, accessTimeLimit: %.1f.\n", 
                1e-6 * db.internal().getStartupPos(), 
                1e-6 * ed.startupPos, 
                1e-6 * db.getStreamLength(), 
                1e-6 * ed.accessTimeLimit);
        System.out.format("cachedMemoryValue: %.1f\n", 1e-6 * db.internal().aux().getCachedMemoryValue());
        System.out.format("not evicted reasons, access time: %d, dirty: %d, not mem: %d.\n", 
                totalReasonAccessTime, totalReasonDirty, totalReasonNotMem);
    }

    private void runGc(CommandLine options) {
        long used1 = memUsed();
        
        for (int i = 0; i < 4; i++) {
            System.gc();
        }
        
        long used2 = memUsed();
        
        System.out.format("Used mem: %.1f MB to %.1f MB.\n",
                1e-6 * (used2 - used1), 
                1e-6 * used2);
    }

    private void runInfo(CommandLine options) {
        int cardCount = getCardCount();
        Runtime runtime = Runtime.getRuntime();
        long maxMem = runtime.maxMemory();
        long freeMem = runtime.freeMemory();
        
        System.out.println("cardCount: " + cardCount);
        System.out.format("JVM memory (MB), max: %.1f, free: %.1f, used: %.1f.\n", 
                1e-6 * maxMem, 1e-6 * freeMem, 1e-6 * (maxMem - freeMem));
        System.out.format("Stream length: %.1f, startupDistance: %.1f, startupPos: %.1f.\n", 
                1e-6 * db.getStreamLength(),
                1e-6 * db.getStartupDistance(),
                1e-6 * db.internal().getStartupPos());
    }
    
    private long memUsed() {
        Runtime r = Runtime.getRuntime();
        long maxMem = r.maxMemory();
        long freeMem = r.freeMemory();
        return maxMem - freeMem;
    }

    private void runAddCards(CommandLine options) {
        computePermutationIfNeeded();
        if (options.hasOne("n")) {
            this.n = Integer.parseInt(options.getOne("n"));
        }
        
        this.addCardsIfNeeded();
    }

    private void start() {
        DatabaseBuilderImp imp = (DatabaseBuilderImp)
                Factory.database().dir(dirname).cryptoKey(cryptoKey)
                .startupDistanceInMb(5);
        
        //imp.evictBoss(new FixedDurationEvictBoss(FixedDurationEvictBoss.suggestCacheDurationBasedOnJvm()));
        //imp.evictBoss(new FixedDurationEvictBoss(25*1000000));
        imp.evictBoss(new FixedDurationEvictBoss(0));
        database = imp.start();
        
        db = ((DatabaseImp) database).getDb();
        
        System.out.format("Database started in %.1f s, dir: %s.\n",
                database.getStartupInfo().getStartupDuration(), dirname);
        
        c = database.connection();
        
        if (!c.exists("/stats")) {
            Stats s = new Stats();
            s.cards = 0;
            c.put("/stats", s);
        }
    }

    private void handleCommandLine(CommandLine line) {
        if (line.hasOne("dir")) {
            this.dirname = line.getOne("dir");
        }
        
        if (line.hasOne("encrypt") && line.getOne("encrypt").equals("true")) {
            cryptoKey = CryptoKey.parse("3925eedf-salsa-9624ae53f2484c7fa8db33141910222b94aa2224ef225bd092d4701d30aa35dbde13575d66982ff9");
        }
    }
    
    private void computePermutationIfNeeded() {
        if (permutation != null) {
            return;
        }
        
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
            
            if (addedCounter % 10000 == 0 && addedCounter > 0) {
                System.out.println("Added " + addedCounter + " cards.");
            }
        }
        
        double time = (System.nanoTime() - t0) * 1e-9;
        
        System.out.format("Added %d cards in %.1f s. %.3f ms per card.\n", 
                addedCounter, time, (time / addedCounter) * 1000.0);
        c.sync();
    }
    
    private int getCardCount() {
        return c.get("/stats", Stats.class).cards;
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

    public static void main(String[] args) throws Exception {
        new Interactive().go(args);
    }
}
