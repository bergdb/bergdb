package bergdb.test.big;

import java.io.File;
import java.util.Random;

import bergdb.core.Db;
import bergdb.core.GetData;
import bergdb.core.Jmx;
import bergdb.core.KeyFactory;
import bergdb.core.Keys;
import bergdb.core.Trans;
import bergdb.stream.FileStream;

/**
 * Creates a database with 100k entries and loads it with get and set transactions, "Load A".
 * 
 * @author Frans Lundberg
 */
public class LoadA {
    private Db db;
    private volatile boolean stop = false;
    private int n = 100*1000;
    
    public void go(String[] args) throws Exception {
        System.out.println("---- " + LoadA.class.getName() + "----");
        String dirname = "temp-LoadA";
        if (args.length > 0) {
            dirname = args[0];
        }
        
        System.out.println("Creating db in dir: " + dirname + ".");
        
        FileStream stream = new FileStream(new File(dirname));
        db = Db.builder().mainStream(stream).start();
        
        System.out.println("DB started, press control-C to exit.");
        
        Jmx.DbMonitor dbMonitor = new Jmx.DbMonitor(db);
        dbMonitor.register();
        Jmx.Speed speed = new Jmx.Speed(db);
        speed.registerAndStart();
        
        System.out.println("Jmx MBeans now active.");
        
        int batchSize = 1000;
        
        for (int i = 0; i < n / batchSize; i++) {
            Trans.Builder b = Trans.builder();
            for (int j = 0; j < batchSize; j++) {
                int keyInt = i * batchSize + j;
                keyInt = keyInt * 10;    // For possibility of inserts between existing keys
                byte[] key = KeyFactory.binaryIntKey(keyInt);
                b.set(key, key);   // key and value is the same
            }
            Trans t = b.build();
            db.execute(t);
        }
        db.sync();
        
        System.out.println("Dummy data created, n = " + n);
        
        Thread t1 = new Thread(new Runnable() {
            public void run() {
                t1Method();
            }
        });
        t1.setName("t1");
        t1.setPriority(Thread.NORM_PRIORITY - 1);
        t1.start();
        
        Thread t2 = new Thread(new Runnable() {
            public void run() {
                t2Method();
            }
        });
        t2.setName("t2");
        t2.setPriority(Thread.NORM_PRIORITY - 1);
        t2.start();
    }
    
    private void t1Method() {
        // Read method
        
        Random r = new Random(1);
        GetData gd = new GetData();
        
        while (!stop) {
            int keyInt = r.nextInt(n) * 10;
            byte[] key = KeyFactory.binaryIntKey(keyInt);
            db.get(Long.MAX_VALUE, Keys.toSegments(key), gd);
            
            try {
                Thread.sleep(10);
            } catch (InterruptedException e) {
                break;
            }
        }
    }
    
    private void t2Method() {
        // Write method, re-writes values.
        
        Random r = new Random(2);
        byte[] value = new byte[1000];
        
        while (!stop) {
            int keyInt = r.nextInt(n) * 10;
            byte[] key = KeyFactory.binaryIntKey(keyInt);
            db.execute(Trans.builder().set(key, value).build());
            
            try {
                Thread.sleep(10);
            } catch (InterruptedException e) {
                break;
            }
        }
    }
    
    public static void main(String[] args) throws Exception {
        new LoadA().go(args);
    }
}
