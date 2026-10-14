package bergdb.test.manual;

import java.io.File;
import java.io.IOException;
import java.util.Calendar;
import java.util.Random;

import bergdb.common.EventToWaitFor;
import bergdb.common.Util;
import bergdb.core.Db;
import bergdb.core.Jmx;
import bergdb.core.KeyFactory;
import bergdb.core.SyncLevel;
import bergdb.core.Trans;
import bergdb.nanotest.SimpleTestEnvironment;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.TestClock;
import bergdb.storage.StreamIoException;
import bergdb.stream.FileStream;

/**
 * Tests maximum throughput of many small, simple transactions.
 * 
 * @author Frans Lundberg
 */
public class TransThroughput {
    private volatile long transCounter = 0;
    private Db db;
    private Trans[] transactions;
    private EventToWaitFor doneEvent;
    private boolean done = false;
    //private final int n = 200*1000;
    private final int n = 1000*1000;
    private final int repetitions = 10;
    private int threadCount;
    
    public TransThroughput() {
        doneEvent = new EventToWaitFor();
    }
    
    private String getTimeString() {
        Calendar c = Calendar.getInstance();
        String result = String.format("%1$tH%1$tM%1$tS%1$tL", c);
        return result;
    }
    
    private void startJmx() throws Exception {
        Jmx.DbMonitor dbMonitor = new Jmx.DbMonitor(db);
        dbMonitor.register();
        Jmx.Speed speed = new Jmx.Speed(db);
        speed.registerAndStart();
        System.out.println("Jmx MBeans now active.");
    }
    
    private void startJmxSilently() {
        try {
            startJmx();
        } catch (Exception e) {
            System.out.println("ERROR, exception when starting JMX.");
            e.printStackTrace(System.out);
        }
    }
    
    private void run(TestEnvironment c, int threadCount) throws IOException, InterruptedException {
        this.threadCount = threadCount;
        
        File temp = File.createTempFile("prefix", "suffix");
        temp.deleteOnExit();
        
        String timeString = getTimeString();
        File dir = new File(temp.getParentFile(), this.getClass().getSimpleName() + "-" + timeString);
        
        c.out().println("TransactionThroughput, dir: " + dir);
        
        FileStream stream = new FileStream(dir);
        TestClock clock = new TestClock();
        db = Db.builder().mainStream(stream).retainForever().noEvict().clock(clock).start();
        
        startJmxSilently();
        System.out.println("JMX started, starting in a few seconds.");
        Thread.sleep(5000);
        
        transactions = new Trans[n];
        Random random = new Random(0);
        
        for (int i = 0; i < n; i++) {
            byte[] key = KeyFactory.binaryIntKey(random.nextInt());
            byte[] value = new byte[0];
            transactions[i] = db.trans().put(key, value).build();
        }
        
        Thread[] threads = new Thread[threadCount];
        for (int i = 0; i < threadCount; i++) {
            final int finalI = i;
            Thread t = new Thread(new Runnable() {
                public void run() {
                    threadWork(finalI);
                }
            });
            
            threads[i] = t;
        }
        
        for (int i = 0; i < threads.length; i++) {
            threads[i].start();
        }
        
        Thread.sleep(200);    // warmup, allows threads to start
        
        long size1 = stream.getLength();
        long t = System.nanoTime();
        long count1 = this.transCounter;
        
        doneEvent.waitForEvent();
        stream.close();
        long size2 = stream.getLength();
        t = System.nanoTime() - t;
        long count2 = this.transCounter;
        
        double transSize = (double)(size2 - size1) / (double) (count2 - count1);
        double streamMBPerSec = (size2 - size1) * 1e-6 / (1e-9 * t);
        
        for (int i = 0; i < threads.length; i++) {
            threads[i].join();
        }
        
        Util.delete(dir);
        
        long count = count2 - count1;
        c.report("transCount", count);
        c.report("time", t*1e-9);
        c.report("timePerTrans", t*1e-9 / count);
        c.report("transPerSec", count / (t*1e-9));
        c.report("transSize", transSize);
        c.report("streamMBPerSec", streamMBPerSec);
    }
    
    private void threadWork(int threadIndex) {
        for (int i0 = 0; i0 < repetitions; i0++) {
            for (int i = threadIndex; i < transactions.length; i += threadCount) {
                try {
                    db.execute(transactions[i]);
                } catch (StreamIoException e) {
                    break;
                }
                
                transCounter++;
                
                if (done) {
                    break;
                }
            }
        }
        
        db.sync(SyncLevel.ORDINARY);
        done = true;
        doneEvent.happened();
    }
    
    @Nano("perf")
    public static void t1(TestEnvironment c) throws IOException, InterruptedException {
        c.out().println("1 thread...");
        new TransThroughput().run(c, 1);
    }
    
    @Nano("perf")
    public static void t2(TestEnvironment c) throws IOException, InterruptedException {
        c.out().println("2 threads...");
        new TransThroughput().run(c, 2);
    }
    
    @Nano("perf")
    public static void t4(TestEnvironment c) throws IOException, InterruptedException {
        c.out().println("4 threads...");
        
        new TransThroughput().run(c, 4);
    }
    
    @Nano("perf")
    public static void t8(TestEnvironment c) throws IOException, InterruptedException {
        c.out().println("8 threads...");
        new TransThroughput().run(c, 8);
    }
    
    public static void main(String[] args) throws IOException, InterruptedException {
        TransThroughput t = new TransThroughput();
        t.run(new SimpleTestEnvironment(), 4);
    }
}

/*

---- 130707 ----
On Cissi, the performance is much better. 
With one thread:   124k trans/s, 60 MB/s.
With four threads: 173k trans/s, 99 MB/s.
Great! I wonder how a more complex transaction would do? Bank payment. And how about using Pub API
instead with object serialization?

---- 130108 ----
On Rose, the best result is 25k trans/s (12 MB/s stream speed).
On Linda (Linode), the best result is 83k trans/s (39 MB/s stream speed).
10k trans/s corresponds to 0.86 G trans/day.
100k trans/s corresponds to 8.6 G trans/day.

Compare with Visa (http://investor.visa.com/phoenix.zhtml?c=215693&p=irol-IRHome):
"Visa has built one of the world’s most advanced processing networks, capable of handling more 
than 10,000 transactions per second, with reliability, convenience and security."

CONCLUSIONS: On a fast server we can run over 100k trans/s for very simple transactions.
For advanced transactions, say payments, we can probably handle 10k payments/s. This is more than
enough for most real-world application I know of. Stock exchange may reach thousands of transactions
per second. Also, Visa/MasterCard may process in that order of transactions per second at peak.

*/