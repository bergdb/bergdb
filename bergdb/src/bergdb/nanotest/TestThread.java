package bergdb.nanotest;

/**
 * Used to create deterministic tests for multithreaded software.
 * 
 * @author Frans Lundberg
 */
public class TestThread extends Thread {
    // Maybe publish to blog.franslundberg.com when tested more.
    
    private final Object sync = new Object();
    private volatile String breakName;
    
    public TestThread() {
        super();
    }
    
    public TestThread(Runnable r) {
        super(r);
    }
    
    /**
     * Run thread until it hits the named breakpoint or exists.
     */
    public void goTo(String breakName) {
        synchronized (sync) {
            this.breakName = breakName;
            sync.notifyAll();
        }
        
        if (getState() == Thread.State.NEW) {
            start();
        }
    }
    
    /**
     * Run thread, not stopping at any break points.
     */
    public void go() {
        goTo(null);
    }
    
    public static boolean breakpoint(String breakName) {
        if (breakName == null) {
            throw new IllegalArgumentException("breakName == null not allowed");
        }
        
        Thread t = Thread.currentThread();
        if (t instanceof TestThread) {
            TestThread my = (TestThread) t;
            synchronized (my.sync) {
                if (my.breakName != null && my.breakName.equals(breakName)) {
                    try {
                        my.sync.wait();
                    } catch (InterruptedException e) {
                        throw new Error("not expected: " + e);
                    }
                }
            }
        }
        
        return true;
    }
    
    /**
     * Try running with and without -ea.
     */
    public static void main(String[] args) throws InterruptedException {
        TestThread t1 = new TestThread(new Runnable() {
            public void run() {
                for (int i = 0; i < 3; i++) {
                    System.out.println("t1: Before " + i);
                    assert TestThread.breakpoint("break-" + i);
                    System.out.println("t1: After " + i);
                    System.out.println();
                }
            }
        });
        
        System.out.println("m: Go to break-0.");
        t1.goTo("break-0");
        Thread.sleep(2000);
        
        System.out.println("m: Go to break-2.");
        t1.goTo("break-2");
        Thread.sleep(2000);
        
        System.out.println("m: go()");
        t1.go();
        
        System.out.println("m: Done!");
    }
}
