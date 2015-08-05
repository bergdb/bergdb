package bergdb.test;

import java.lang.Thread.UncaughtExceptionHandler;
import java.lang.management.ManagementFactory;
import java.util.Random;
import java.util.concurrent.atomic.AtomicLong;

import javax.management.InstanceAlreadyExistsException;
import javax.management.MBeanRegistrationException;
import javax.management.MBeanServer;
import javax.management.MalformedObjectNameException;
import javax.management.NotCompliantMBeanException;
import javax.management.ObjectName;

import bergdb.core.Db;
import bergdb.core.FixedDurationEvictBoss;
import bergdb.core.Jmx;
import bergdb.nanotest.Assert;
import bergdb.nanotest.BasicTestEnvironment;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.Action;
import bergdb.pub.Clock;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.ReadInterface;
import bergdb.pub.RwEnvironment;
import bergdb.pub.Time;
import bergdb.pub.WBuilder;
import bergdb.pubimp.DatabaseBuilderImp;
import bergdb.pubimp.DatabaseImp;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.DummyStream;

/**
 * Tests the concurrency of the database.
 * 
 * @author Frans Lundberg
 */
public class Concurrency {
    private Database database;
    private volatile boolean stop = false;
    private static final int accounts = 10;
    private final AtomicLong transCount = new AtomicLong(0);
    private final AtomicLong readCount = new AtomicLong(0);
    private volatile long transPerSec;
    private volatile long opsPerSec;
    private volatile Throwable exception = null;
        // Exception from any started thread.
    
    public Concurrency() throws Exception {
        AppendOnlyStream stream = new DummyStream();
        DatabaseBuilderImp builder = (DatabaseBuilderImp) Factory.database();
        builder.mainStream(stream);
        builder.evictBoss(new FixedDurationEvictBoss(100L*1000000));
        
        Db db = ((DatabaseImp) database).getDb();
        db.setRetainDuration(10 * Clock.UNITS_PER_SEC);
        database = builder.start();
        new Jmx.DbMonitor(db).register();
        new Jmx.Speed(db).registerAndStart();
    }
    
    public void go(TestEnvironment env, int secondsToRun) throws Throwable {
        env.out().println("Running 4 readers and 4 writers. 10 accounts, checking sum.");
        
        final Random random = new Random();
        UncaughtExceptionHandler handler = new UncaughtExceptionHandler() {
            public void uncaughtException(Thread t, Throwable e) {
                e.printStackTrace();
                exception = e;
            }
        };
        
        Thread[] writers = new Thread[4];
        for (int i = 0; i < writers.length; i++) {
            Thread t = new Thread(new Runnable() {
                public void run() {
                    writer(random.nextLong());
                }
            });
            t.setName("w" + i);
            t.setUncaughtExceptionHandler(handler);
            writers[i] = t;
        }
        
        Thread[] readers = new Thread[4];
        for (int i = 0; i < writers.length; i++) {
            Thread t = new Thread(new Runnable() {
                public void run() {
                    reader();
                }
            });
            t.setName("r" + i);
            t.setUncaughtExceptionHandler(handler);
            readers[i] = t;
        }
        
        Connection c = database.newConnection();
        
        WBuilder b = c.w();
        
        for (int i = 0; i < accounts; i++) {
            String key = "" + i;
            b.put(key, "0");
        }
        b.put("99", "0");         // Transaction count.
        b.execute();        
        for (Thread t : readers) t.start();
        for (Thread t : writers) t.start();
        
        long lastTransCount = 0;
        long lastReadCount = 0;
        int pauseDuration = 4;
        int timesToRun = (int) Math.ceil(((double) secondsToRun) / pauseDuration);
        
        try {
            for (int i = 0; i < timesToRun; i++) {
                long t0 = System.nanoTime();
                
                Thread.sleep(pauseDuration * 1000);
                if (exception != null) {
                    break;
                }
                
                double time = (System.nanoTime() - t0) * 1e-9;
                
                long tCount = transCount.get();
                long rCount = readCount.get();
                transPerSec = (long) ((tCount - lastTransCount) / time);
                long readsPerSec = (long) ((rCount - lastReadCount) / time);
                lastTransCount = tCount;
                lastReadCount = rCount;
                opsPerSec = transPerSec + readsPerSec;
                
                env.out().println("i = " + i + ", tCount = " + transCount 
                        + ", trans/s: " + transPerSec 
                        + ", reads/s: " + readsPerSec 
                        + ", ops/s: " + opsPerSec);
            }
        } finally {
            stop = true;
            for (Thread t : readers) t.join();
            for (Thread t : writers) t.join();
        }
        
        if (exception != null) {
            throw exception;
        }
    }
    
    private void writer(long seed) {
        Random random = new Random(seed);
        Connection c = database.newConnection();
        
        while (!stop) {
            makePayment(c, random);
            transCount.incrementAndGet();
        }
    }
    
    private void makePayment(Connection c, Random random) {
        final int account1 = random.nextInt(accounts/2);
        final int account2 = random.nextInt(accounts/2) + accounts/2;
        
        c.rw(new Action() {
            public void run(RwEnvironment env) {
                long balance1 = readLong(env, account1);
                long balance2 = readLong(env, account2);
                long count = readLong(env, 99);
                env.put("" + account1, "" + (balance1 - 2));
                env.put("" + account2, "" + (balance2 + 2));
                env.put("99", "" + (count + 1));
            }
        });
    }
    
    private long readLong(ReadInterface r, int account) {
        String key = "" + account;
        String s = r.get(key, String.class);
        String s2 = r.get(key, String.class);
        String s3 = r.get(key, String.class);
        
        if (s == null) {
            String message = "No value for key '" + key + "'.";
            
            System.out.println("ERROR: " + message);
            System.out.println("s2 = " + s2);
            System.out.println("s3 = " + s3);
            
            System.out.println("---- State ----");
            printState(r);
            throw new RuntimeException(message);
        }
        
        long result;
        result = Long.parseLong(s);
        return result;
    }
    
    /**
     * Checks the expected invariants.
     */
    private void reader() {
        try {
            Connection c = database.newConnection();
            System.out.println("Reader connection: " + c + ", thread: " + Thread.currentThread().getName());
            while (!stop) {
                readerInner(c);
            }
        } catch (Exception e) {
            this.exception = e;
        }
    }
    
    private void printState(ReadInterface c) {
        for (int i = 0; i < accounts; i++) {
            System.out.println(i + ": " + readLong(c, i));
        }
        System.out.println("this.transCount = " + this.transCount.get());
    }
    
    private void readerInner(Connection c) {
        
        c.freezeLookupTime();
        
        // Check sum of accounts == 0.
        
        long sum = 0;
        
        for (int i = 0; i < accounts; i++) {
            sum += readLong(c, i);
        }
        
        Assert.assertEquals(0, sum);
        
        // Check count and sum first half, second half
        
        int half = accounts / 2;
        long sum1 = 0;
        long sum2 = 0;
        
        for (int i = 0; i < half; i++) {
            sum1 += readLong(c, i);
        }
        
        for (int i = half; i < accounts; i++) {
            sum2 += readLong(c, i);
        }
        
        long count = readLong(c, 99);
        
        Assert.assertEquals(-sum1, sum2);
        Assert.assertEquals(-count * 2, sum1);
        Assert.assertEquals(count * 2, sum2);
        
        c.setLookupTime(Time.MAX);
        this.readCount.incrementAndGet();
    }
    
    @Nano("f")
    public static void t1(TestEnvironment env) throws Throwable {
        new Concurrency().go(env, 10);
    }
    
    public static void main(String[] args) throws Throwable {
        Thread.setDefaultUncaughtExceptionHandler(new UncaughtExceptionHandler() {
            public void uncaughtException(Thread t, Throwable e) {
                e.printStackTrace();
                System.exit(1);
            }
        });
        
        Concurrency c = new Concurrency();
        Monitor m = new Monitor(c);
        m.register();
        
        c.go(new BasicTestEnvironment(), Integer.MAX_VALUE);
    }
    
    public static class Monitor implements MonitorMBean {
        Concurrency c;
        
        public Monitor(Concurrency c) {
            this.c = c;
        }

        public long getOpsPerSec() {
            return c.opsPerSec;
        }
        
        public long getTransPerSec() {
            return c.transPerSec;
        }
        
        public void register() throws InstanceAlreadyExistsException, 
            MBeanRegistrationException, NotCompliantMBeanException, 
            MalformedObjectNameException, NullPointerException {
            MBeanServer mbs = ManagementFactory.getPlatformMBeanServer();
            mbs.registerMBean(this, new ObjectName("com.bergdb.test.Concurrency:type=Concurrency.Monitor"));
        }
    }
    
    public static interface MonitorMBean {
        public long getOpsPerSec();
        public long getTransPerSec();
    }
}


/*

130129 on linda
===============

Ran on linda (linode.com, London). Sustained rate of 25000 ops/s and 11000 trans/s for over 1 h.
Command:

    java -Xmx200m -server -cp bergdb.jar com.bergdb.test.Concurrency &
    
Memory use: heap up to 60 MB (= 60e6 B). Size 72 MB (allocated). PermGen 22 MB.
According to top, the process uses 100m of memory and nearly 300% of CPU (4 cores, I believe).
More stable memory consumption then on rose. "GC activity" is typically 4%.


130128 on rose
==============

Run for over 1 h on Rose. Sustained rate of over 5000 ops/s and 3500 trans/s.
Great! DB.evictInner() runs once per 100 Get ops. It keep memory bounded. After GC we have around
60 MB of memory use. noReclaim, FixedDurationEvictBoss() (default: duration = 0.25 * 500M = 125 M).
A higher memory use (after GC) was expected.

    // evictInner() ran every 100th get().
    FixedDurationEvictionBoss.evictOrNot() {
        return counter++ % 100 == 0;
    }
    
1 of 100 is enough for this particular load.
*/