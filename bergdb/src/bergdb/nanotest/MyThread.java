package bergdb.nanotest;

/**
 * Used to create deterministic tests for multithreaded software.
 * 
 * @author Frans Lundberg
 */
public class MyThread extends Thread {
    // If this little code works out well, maybe I should publish to blog.franslundberg.com.
    
    private final Object sync = new Object();
    private volatile String breakName;
    
    public MyThread() {
        super();
    }
    
    public MyThread(Runnable r) {
        super(r);
    }
    
    /**
     * Run thread till the named breakpoint.
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
        if (t instanceof MyThread) {
            MyThread my = (MyThread) t;
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
        MyThread t1 = new MyThread(new Runnable() {
            public void run() {
                for (int i = 0; i < 3; i++) {
                    System.out.println("t1: Before " + i);
                    assert MyThread.breakpoint("break-" + i);
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
