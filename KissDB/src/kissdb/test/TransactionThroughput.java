package kissdb.test;

import java.io.File;
import java.io.IOException;
import java.util.Calendar;
import java.util.Random;

import kissdb.common.EventToWaitFor;
import kissdb.common.Util;
import kissdb.core.Db;
import kissdb.core.KeyFactory;
import kissdb.core.NoEvictBoss;
import kissdb.core.Trans;
import kissdb.nanotest.TestCollector;
import kissdb.nanotest.T;
import kissdb.pub.TestClock;
import kissdb.storage.BufferedStream;
import kissdb.storage.StreamIoException;
import kissdb.stream.FileStream;

/**
 * Tests maximum throughput of many small transactions.
 * 
 * @author Frans Lundberg
 */
public class TransactionThroughput {
    private volatile long transCounter = 0;
    private Db db;
    private Trans[] transactions;
    private EventToWaitFor doneEvent;
    private boolean done = false;
    private final int n = 200*1000;
    private int threadCount;
    
    public TransactionThroughput() {
        doneEvent = new EventToWaitFor();
    }
    
    private String getTimeString() {
        Calendar c = Calendar.getInstance();
        String result = String.format("%1$tH%1$tM%1$tS%1$tL", c);
        return result;
    }
    
    private void run(TestCollector c, int threadCount) throws IOException, InterruptedException {
        this.threadCount = threadCount;
        
        File temp = File.createTempFile("prefix", "suffix");
        temp.deleteOnExit();
        
        String timeString = getTimeString();
        File dir = new File(temp.getParentFile(), this.getClass().getSimpleName() + "-" + timeString);
        
        c.out().println("TransactionThroughput, dir: " + dir);
        
        FileStream m = new FileStream(dir);
        BufferedStream b = new BufferedStream(m, 20*1000000, 100);
        b.start();
        TestClock clock = new TestClock();
        db = Db.builder().mainStream(b).retainForever().evictBoss(new NoEvictBoss()).clock(clock).start();
        
        transactions = new Trans[n];
        Random random = new Random(0);
        
        for (int i = 0; i < n; i++) {
            byte[] key = KeyFactory.binaryIntKey(random.nextInt());
            byte[] value = new byte[0];
            transactions[i] = Trans.builder().set(key, value).build();
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
        
        long size1 = b.getLength();
        long t = System.nanoTime();
        long count1 = this.transCounter;
        
        doneEvent.waitForEvent();
        b.close();
        long size2 = b.getLength();
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
        
        done = true;
        doneEvent.happened();
    }
    
    @T("perf")
    public static void t1(TestCollector c) throws IOException, InterruptedException {
        c.out().println("1 thread...");
        new TransactionThroughput().run(c, 1);
    }
    
    @T("perf")
    public static void t2(TestCollector c) throws IOException, InterruptedException {
        c.out().println("2 threads...");
        new TransactionThroughput().run(c, 2);
    }
    
    @T("perf")
    public static void t4(TestCollector c) throws IOException, InterruptedException {
        c.out().println("4 threads...");
        new TransactionThroughput().run(c, 4);
    }
    
    @T("perf")
    public static void t8(TestCollector c) throws IOException, InterruptedException {
        c.out().println("8 threads...");
        new TransactionThroughput().run(c, 8);
    }
}

/*

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
enough for any real-world application I know of. Stock exchange may reach thousands of transactions
per second. Also, Visa/MasterCard may process in that order of transactions per second at peak.

*/