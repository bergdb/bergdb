package bergdb.common;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * An event that a thread can wait for to happen.
 * Simple thread synchronization.
 * 
 * @author Frans Lundberg
 */
public class EventToWaitFor {
    // Also see version in Github, java-cut.
    
    private boolean hasHappened = false;

    /**
     * Tells this object that the event has occurred.
     */
    public synchronized void happened() {
        hasHappened = true;
        notifyAll();
    }

    /**
     * Waits for event to occur, or returns immediately if it has occurred. The
     * method also returns immediately if the calling thread is interrupted.
     * Waits indefinitely.
     */
    public synchronized void waitForEvent() {
        waitForEvent(0);
    }

    /**
     * Waits for event to occur, or returns immediately if it has occurred. The
     * method also returns immediately if the calling thread is interrupted.
     * Waiting is constrained by the time parameter, 0 for no limit. A spurious
     * wakeup waits on until the event or the end of the time (bergdb 021-28).
     * 
     * @param time Maximum time to wait in milliseconds.
     */
    public synchronized void waitForEvent(long time) {
        final long end = System.nanoTime() + time * 1000000L;
        try {
            while (!hasHappened) {
                if (time == 0) {
                    wait();
                } else {
                    long ms = (end - System.nanoTime() + 999999) / 1000000;
                    if (ms <= 0) {
                        return;
                    }
                    wait(ms);
                }
            }
        } catch (InterruptedException e) {
            // Silently ignore. We were stopped by another thread
        }
    }

    /**
     * Returns true if the event actually happened.
     * 
     * @return true if happened.
     */
    public synchronized boolean didItHappen() {
        return hasHappened;
    }
    
    @Nano
    private static void test1() {
        EventToWaitFor event = new EventToWaitFor();
        Assert.assertFalse(event.didItHappen());
        event.happened();
        Assert.assertTrue(event.didItHappen());
    }
    
    @Nano
    private static void test2() {
        final EventToWaitFor event = new EventToWaitFor();
        // The thread waits for 'go' (bergdb 021-28): with a sleep of 10 ms only, a loaded
        // machine could run it before the second assertFalse.
        final java.util.concurrent.CountDownLatch go = new java.util.concurrent.CountDownLatch(1);
        Thread t = new Thread(new Runnable() {
            public void run() {
                try {
                    go.await();
                    Thread.sleep(10);
                } catch (InterruptedException e) {
                    // empty
                }
                
                event.happened();
            }
        });
        t.setPriority(Thread.MAX_PRIORITY);
        
        Assert.assertFalse(event.didItHappen());
        t.start();
        Assert.assertFalse(event.didItHappen());
        go.countDown();
        event.waitForEvent(60_000);
        Assert.assertTrue("event did not happen within 60 s", event.didItHappen());
    }
}
