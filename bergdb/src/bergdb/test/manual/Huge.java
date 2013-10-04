package bergdb.test.manual;

import java.io.File;
import java.io.IOException;
import java.util.Random;

import bergdb.core.Db;
import bergdb.core.DbUtil;
import bergdb.core.Jmx;
import bergdb.core.KeyFactory;
import bergdb.core.Trans;
import bergdb.coreds.GetData;
import bergdb.coreds.Keys;
import bergdb.stream.FileStream;

/**
 * This executable class is used to create a huge database and test read performance on it.
 * Trying to push the limits.
 * 
 * @author Frans Lundberg
 */
public class Huge {
    private int n;     // kvs in database
    
    public void create(String dirname, int n) throws Exception {
        if (n == 0) {
            n = 10*1000000;
        }
        
        int batchSize = 1000;   // batch size
        
        System.out.println("Creating DB of size " + (1e-6 * n) + "M to dir " + dirname + ".");
        
        FileStream stream = new FileStream(new File(dirname));
        Db db = Db.builder().mainStream(stream).startupDistance(40*1000000).build();
        db.start();
        
        db.execute(Trans.builder().put("n", "" + n).build());
        System.out.println("Wrote n = " + n + " to database.");
        
        int kvCount = 0;
        
        if (batchSize > n) {
            batchSize = (int) n;
        }
        assert n % batchSize == 0;
        
        Jmx.DbMonitor dbMonitor = new Jmx.DbMonitor(db);
        dbMonitor.register();
        Jmx.Speed speed = new Jmx.Speed(db);
        speed.registerAndStart();
        
        System.out.println("Jmx MBeans now active.");
        System.out.println("Waiting 20 s to allow monitor tools to be started.");
        Thread.sleep(20*1000);
        System.out.println("Starting.");
        
        long nanos = System.nanoTime();
        long periodStartTime = System.nanoTime();
        long periodKvCount = 0;
        
        for (int i = 0; i < n / batchSize; i++) {
            Trans.Builder b = Trans.builder();
            for (int j = 0; j < batchSize; j++) {
                int keyInt = i * batchSize + j;
                keyInt = keyInt * 2;    // For possibility of inserts between existing keys
                byte[] key = KeyFactory.binaryIntKey(keyInt);
                b.put(key, key);   // key and value is the same
            }
            Trans t = b.build();
            db.execute(t);
            kvCount += batchSize;
            periodKvCount += batchSize;
            
            long now = System.nanoTime();
            long periodTime = now - periodStartTime;
            if (periodTime * 1e-9 > 4.0) {
                double timePerKv = periodTime * 1e-9 / periodKvCount;
                System.out.printf("kvCount: %d, timePerKv: %.6f\n", kvCount, timePerKv);
                
                // We reported a period (ended it), let's start a new period.
                periodStartTime = now;
                periodKvCount = 0;
            }
        }
        
        nanos = System.nanoTime() - nanos;
        db.sync();
        db.stop();
        
        long streamLength = stream.getLength();
        double time = nanos * 1e-9;
        double timePerKv = time / n;
        
        System.out.println();
        System.out.println("Done!");
        System.out.printf("Total time: %.1f s\n", time);
        System.out.printf("Time per kv: %.3g\n", timePerKv);
        System.out.printf("Total stream length: %dM\n", (streamLength / (1*1000000)));
    }
    
    public void n(String dirname) throws IOException {
        FileStream stream = new FileStream(new File(dirname));
        Db db = Db.builder().mainStream(stream).startupDistance(40*1000000).build();
        
        long nanos = System.nanoTime();
        db.start();
        nanos = System.nanoTime() - nanos;
        
        System.out.printf("Startup time: %.1f s\n", (nanos * 1e-9));
        
        String nString = DbUtil.getString(db, "n");
        db.stop();
        
        System.out.println("n = " + nString);
    }
    
    public void runGetOps(String dirname, IntFactory intFactory) throws IOException {
        FileStream stream = new FileStream(new File(dirname));
        Db db = Db.builder().mainStream(stream).startupDistance(40*1000000).build();
        
        long nanos = System.nanoTime();
        db.start();
        nanos = System.nanoTime() - nanos;
        
        System.out.printf("Startup time: %.1f s\n", (nanos * 1e-9));
        
        GetData gd = new GetData();
        
        String nString = DbUtil.getString(db, "n");
        if (nString == null) {
            n = 10*1000000;    // default
            System.out.println("default n = " + n);
        } else {
            n = Integer.parseInt(nString);
            System.out.println("n from database.");
        }
        
        System.out.printf("n: %d = %.2g\n", n, (double) n);
        
        System.out.println("Output per batch. One batch about every 2 seconds.");
        System.out.println("  count: total number of get operation so far.");
        System.out.println("  timePerGet: average time per get (s).");
        System.out.println("  stream: average stream node accesses (stream reads) per get");
        System.out.println("  mem: average memory node accesses per get");
        
        long totalCount = 0;
        //long totalTimeStart = System.nanoTime();
        byte[] value;
        
        A: while (true) {
            long batchTime = System.nanoTime();
            long batchCount = 0;
            gd.followMemoryPointerCount = 0;
            gd.followStreamPointerCount = 0;
            
            while (true) {
                int intKey = intFactory.nextInt(n);
                
                long[] key = Keys.toSegments(KeyFactory.binaryIntKey(intKey));
                value = db.getOne(Long.MAX_VALUE, key, gd);
                if (value == null) {
                    throw new AssertionError("value == null for " + intKey);
                }
                batchCount++;
                
                // If enough time has elapsed (2.0 s), consider it "batch done" and 
                // print info.
                
                if (batchCount % 10 == 0) {
                    long now = System.nanoTime();
                    if ((now - batchTime) * 1e-9 > 2.0) {
                        batchTime = now - batchTime;
                        totalCount += batchCount;
                        //double totalTimeNow = now - totalTimeStart;
                        double timePerGet = (batchTime * 1e-9) / batchCount;
                        //double totalTimePerGet = (totalTimeNow * 1e-9) / totalCount;
                        double streamAccessCountPerGet = ((double) gd.followStreamPointerCount) / batchCount;
                        double memAccessCountPerGet = ((double) gd.followMemoryPointerCount) / batchCount; 
                        
                        System.out.printf("count: %d, timePerGet: %.6f, stream: %.6f, mem: %.2f.\n", 
                                totalCount, timePerGet, streamAccessCountPerGet, memAccessCountPerGet);
                        continue A;
                    }
                }
            }
        }
    }
    
    public static interface IntFactory {
        public int nextInt(int n);     // n = size of database
    }

    /**
     * Handles command line args.
     * 
     * @throws IOException 
     */
    public void go(String[] args) throws Exception {
        if (args.length == 0 || args.length > 0 && args[0].equals("help")) {
            System.out.println("Usage:");
            System.out.println("  ..Huge help             -- prints this");
            System.out.println("  ..Huge create <dir> <n> -- creates db in the specified directory");
            System.out.println("  ..Huge n <dir>          -- Prints size of db (number of entries)");
            System.out.println("  ..Huge random <dir>     -- random KV access to db in specified dir");
            System.out.println("  ..Huge random0.1 <dir>    -- random KV access to 0.1% of db in specified dir");
            System.out.println("  ..Huge random1 <dir>    -- random KV access to 1% of db in specified dir");
            System.out.println("  ..Huge random10 <dir>   -- random KV access to 10% of db in specified dir");
            return;
        }
        
        String command = args[0];
        if (command.equals("create")) {
            if (args.length < 3) {
                System.out.println("ERROR, missing directory / size params.");
                return;
            }
            
            create(args[1], (int) (Double.parseDouble(args[2])));
        } else if (command.startsWith("random")) {
            if (args.length < 2) {
                System.out.println("ERROR, missing directory.");
                return;
            }
            
            //final Random r = new Random(1);
            final Random r = new Random();
            
            if (command.equals("random")) {
                runGetOps(args[1], new IntFactory() { 
                    public int nextInt(int n) {
                        return r.nextInt(n) * 2;                 // 100 percent
                    }
                });
            } else if (command.equals("random10")) {
                runGetOps(args[1], new IntFactory() { 
                    public int nextInt(int n) {
                        return (r.nextInt(n/10) + n/2) * 2;      //  10 percent in the middle
                    }
                });
            } else if (command.equals("random1")) {
                runGetOps(args[1], new IntFactory() { 
                    public int nextInt(int n) {
                        return (r.nextInt(n / 100) + n/2) * 2;  //   1 percent in the middle
                    }    
                });
            } else if (command.equals("random0.1")) {
                runGetOps(args[1], new IntFactory() { 
                    public int nextInt(int n) {
                        return (r.nextInt(n / 1000) + n/2) * 2;  //  0.1 percent in the middle
                    }
                });
            } else {
                System.out.println("ERROR, unrecognized command: " + command + ".");
                return;
            }
        } else if (command.equals("n")) {
            n(args[1]);
            return;
        }
         else {
            System.out.println("ERROR, command '" + command + "' not recognized.");
            return;
        }
    }
    
    public static void main(String[] args) throws Exception {
        new Huge().go(args);
    }
}
