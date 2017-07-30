package bergdb.test.manual;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Random;
import bergdb.common.Bytes;
import bergdb.common.Util;
import bergdb.core.Db;
import bergdb.core.Jmx;
import bergdb.dag.Dag;
import bergdb.dag.Node;
import bergdb.dag.Pointer;
import bergdb.dag.PointerVisitor;
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
    private String dirname;
    private CryptoKey cryptoKey;
    private Database database;
    private Db db;
    private BufferedReader reader;
    int[] permutation = null;   // card permutation
    static final int MAX = 1 * 1000000;
    private Connection c;
    int n = 100*1000;   // wanted number of cards
    private int cacheSize = 100;         // in MB
    private int startupDistance = 5;     // in MB
    
    private void go(String[] args) throws Exception {
        CommandLine line = new CommandLine(args);
        
        if (line.has("help")) {
            printHelp();
            return;
        }
        
        handleOptions(line);
        start();
        runInteractively();
    }
    
    private void printHelp() {
        System.out.println("Options:");
        System.out.println("  -dir <db-dir>");
        System.out.println("  -encrypt <true-or-false>  // default is false");
        System.out.println("  -cacheSize <cache size indicator in MB> // default is 100 MB.");
    }

    private void handleOptions(CommandLine line) {
        dirname = "Interactive-db";
        cryptoKey = CryptoKey.NULL;
        
        if (line.hasOne("dir")) {
            this.dirname = line.getOne("dir");
        }
        
        if (line.hasOne("encrypt") && line.getOne("encrypt").equals("true")) {
            cryptoKey = CryptoKey.parse("3925eedf-salsa-9624ae53f2484c7fa8db33141910222b94aa2224ef225bd092d4701d30aa35dbde13575d66982ff9");
        }
        
        if (line.hasOne("cacheSize")) {
            cacheSize = Integer.parseInt(line.getOne("cacheSize"));
        }
        
        if (line.hasOne("startupDistance")) {
            startupDistance = Integer.parseInt(line.getOne("startupDistance"));
        }
    }

    private void start() throws Exception {
        DatabaseBuilderImp imp = (DatabaseBuilderImp)
                Factory.database().dir(dirname).cryptoKey(cryptoKey)
                .startupDistanceInMb(startupDistance).cacheSizeInMb(cacheSize);
        
        database = imp.start();
        
        db = ((DatabaseImp) database).getDb();
        
        System.out.format("Database started in %.1f s, dir: %s.\n",
                database.getStartupInfo().getStartupDuration(), dirname);
        
        System.out.println("cacheSize: " + cacheSize);
        System.out.println("size indicator: " + db.internal().cache().getSizeIndicator());
        
        c = database.connection();
        
        if (!c.exists("/stats")) {
            Stats s = new Stats();
            s.cards = 0;
            c.put("/stats", s);
        }
        
        new Jmx.DbMonitor(db).register();
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
            System.out.println("Help... try one of addCards, exit, info, gc, gc2, evictMax, addBig, addSmall");
        } else if (commandName.equals("addCards")) {
            runAddCards(options);
        } else if(commandName.equals("exit")) {
            shouldExit = true;
        } else if(commandName.equals("info")) {
            runInfo(options);
        } else if(commandName.equals("gc")) {
            runGc(options);
        } else if(commandName.equals("evictMax")) {
            runEvictMax(options);
        } else if(commandName.equals("addBig")) {
            runAddBig(options);
        } else if(commandName.equals("addSmall")) {
            runAddSmall(options);
        } else {
            System.out.println("Unknown command.");
        }
        
        return shouldExit;
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
        long totalMem = runtime.totalMemory();
        long freeMem = runtime.freeMemory();
        long maxMem = runtime.maxMemory();
        
        System.out.println("cardCount: " + cardCount);
        System.out.format("JVM memory (MB), max: %.1f, used: %.1f.\n", 
                1e-6 * maxMem, 1e-6 * (totalMem - freeMem));
        System.out.format("Stream length: %.1f, startupDistance: %.1f, startupPos: %.1f.\n", 
                1e-6 * db.getStreamLength(),
                1e-6 * db.getStartupDistance(),
                1e-6 * db.internal().getStartupPosForEvict());
        System.out.format("Cache, totalSize: %d, putSize: %d\n", 
                db.internal().cache().totalSize(), 
                db.internal().cache().putSize());
    }
    
    private void runEvictMax(CommandLine options) {
        // Bulk evict is of interest, a pointer can be processed in 0.25 us.
        
        final Dag dag = db.internal().dag();
        final long[] counters = new long[7];
        long t0 = System.nanoTime();
        
        PointerVisitor visitor = new PointerVisitor() {
            
            public void visitPointer(Node from, Pointer pointer) {
                synchronized (db.internal().getPointerLock(from, pointer.index)) {
                    Node pointee = pointer.node;
                    
                    if (pointee != null && !pointee.isDirty()) {
                        from.setPointer(pointer.index, null, pointee.getSpos());
                        
                        counters[1]++;
                        
                        switch (pointee.getType()) {
                        case Node.TYPE_TOP_NODE:
                            counters[2]++;
                            break;
                        case Node.TYPE_KEY_NODE:
                            counters[3]++;
                            break;
                        case Node.TYPE_VALUE:
                            counters[4]++;
                            break;
                        }
                    }
                    
                    counters[0]++;
                }
            }

            public void visitNode(Node node) {
                counters[5]++;
                
                if (node.isIndexNode()) {
                    counters[6]++;
                }
            }
        };
        
        dag.visitMemoryPointersOnce(visitor);
        
        // Note, the visitMemoryPointersOnce() is actually faster (-20%).
        // No need to traverse DAG and allow duplicate visits.
        
        double time = 1e-9 * (System.nanoTime() - t0);
        
        System.out.format("Evicted %d pointers out of %d visited.\n", counters[1], counters[0]);
        System.out.format("In %.3f s, %.2f us per pointer visited, %.2f us per evicted pointer.\n",
                time, 1e6 * time / counters[0], 1e6 * time / counters[1]);
        System.out.format("Nodes visited: %d (%.2f us per node)\n", 
                counters[5], 1e6 * time / counters[5]);
        System.out.format("Index nodes visited: %d (%.2f us per index node)\n",
                counters[6], 1e6 * time / counters[6]);
        System.out.format("Evicted node types, top: %d, key: %d, value: %d.\n", 
                counters[2], counters[3], counters[4]);
    }
    
    private void runAddBig(CommandLine options) {
        int n = 1;
        int size = 1*1000000;
        
        if (options.hasOne("n")) {
            n = Integer.parseInt(options.getOne("n"));
        }
        
        if (options.hasOne("size")) {
            size = Integer.parseInt(options.getOne("size"));
        }
        
        for (int i = 0; i < n; i++) {
            String key = "/big/" + i;
            byte[] value = new byte[size];
            c.put(key, value);
        }
        
        c.sync();
    }
    
    private void runAddSmall(CommandLine options) {
        int n = 1000;
        
        if (options.hasOne("n")) {
            n = Integer.parseInt(options.getOne("n"));
        }
        
        for (int i = 0; i < n; i++) {
            String key = "/small/" + i;
            byte[] value = new byte[10];
            c.put(key, value);
        }
        
        c.sync();
    }

    private long memUsed() {
        Runtime r = Runtime.getRuntime();
        return r.totalMemory() - r.freeMemory();
    }

    private void runAddCards(CommandLine options) {
        computePermutationIfNeeded();
        if (options.hasOne("n")) {
            this.n = Integer.parseInt(options.getOne("n"));
        }
        
        this.addCardsIfNeeded();
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
            
            if (addedCounter % 20000 == 0 && addedCounter > 0) {
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
