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
     * Waiting is constrained by the time parameter.
     * 
     * @param time Maximum time to wait in milliseconds.
     */
    public synchronized void waitForEvent(long time) {
        try {
            if (!hasHappened) {
                wait(time);
                if (!hasHappened) {
                    return;
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
        Thread t = new Thread(new Runnable() {
            public void run() {
                try {
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
        event.waitForEvent(60_000);
        Assert.assertTrue("event did not happen within 60 s", event.didItHappen());
    }
}
