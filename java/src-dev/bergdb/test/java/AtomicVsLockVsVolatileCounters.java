package bergdb.test.java;

import java.util.concurrent.atomic.AtomicLong;

import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;

/**
 * Compares performance of a counter that uses AtomicLong versus one that uses a lock object
 * and a synchronized block versus one that uses volatile.
 * 
 * @author Frans Lundberg
 */
public class AtomicVsLockVsVolatileCounters {
    private long counter = 0;
    private final Object counterLock = new Object();
    
    private AtomicLong atomicCounter = new AtomicLong(0);
    
    private volatile long volatileCounter = 0;
        // Note, with volatile, we may miss updates.
    
    AtomicVsLockVsVolatileCounters() {
    }
    
    void withAtomic(TestEnvironment c, int n) {
        assert n >= 100 || n % 4 == 0;
        
        for (int i = 0; i < n; i++) {
            atomicCounter.incrementAndGet();
        }
        
        atomicCounter.set(0);
        
        long time = System.nanoTime();
        for (int i = 0; i < n / 4; i++) {
            atomicCounter.incrementAndGet();
        }
        time = System.nanoTime() - time;
        double timePerCount = 1e-9 * time / n;
        
        c.report("timePerCount", timePerCount);
    }
    
    void withLock(TestEnvironment c, int n) {
        assert n >= 100 || n % 4 == 0;
        
        for (int i = 0; i < n; i++) {
            synchronized (counterLock) {
                counter++;
            }
        }
        
        counter = 0;
        
        long time = System.nanoTime();
        for (int i = 0; i < n; i++) {
            synchronized (counterLock) {
                counter++;
            }
        }
        time = System.nanoTime() - time;
        double timePerCount = 1e-9 * time / n;
        
        assert counter == n;
        c.report("timePerCount", timePerCount);
    }
    
    void withVolatile(TestEnvironment c, int n) {
        assert n >= 100 || n % 4 == 0;
        
        for (int i = 0; i < n; i++) {
            volatileCounter++;
        }
        
        volatileCounter = 0;
        
        long time = System.nanoTime();
        for (int i = 0; i < n; i++) {
            volatileCounter++;
        }
        time = System.nanoTime() - time;
        double timePerCount = 1e-9 * time / n;
        
        assert volatileCounter == n;
        c.report("timePerCount", timePerCount);
    }
    
    @Nano("perf")
    public static void atomic(TestEnvironment c) {
        new AtomicVsLockVsVolatileCounters().withAtomic(c, 10*1000000);
    }
    
    @Nano("perf")
    public static void lock(TestEnvironment c) {
        new AtomicVsLockVsVolatileCounters().withLock(c, 10*1000000);
    }
    
    @Nano("perf")
    public static void volatileCounter(TestEnvironment c) {
        new AtomicVsLockVsVolatileCounters().withVolatile(c, 10*1000000);
    }
}

/*

130201 Frans: 

On rose, atomic.timePerCount = 8 ns, lock.timePerCount = 40 ns, volatileCounter.timePerCount = 16 ns.
On linda, atomic.timePerCount = 3.9 ns, lock.timePerCount = 33 ns.
Conclusion: AtomicLong is fast! Even faster than volatile. Note that the volatile counter
is functionally inferior since it can miss updates.

Code (http://fuseyism.com/classpath/doc/java/util/concurrent/atomic/AtomicLong-source.html):

    public final long incrementAndGet() {
        for (;;) {
            long current = get();
            long next = current + 1;
            if (compareAndSet(current, next))
                return next;
            }
        }
    }
 
Most methods of AtomicLong calls compareAndSet.

*/