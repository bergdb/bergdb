package bergdb.test;

import bergdb.common.Util;
import bergdb.core.Db;
import bergdb.dag.GetData;
import bergdb.dag.Keys;
import bergdb.nanotest.BasicTestEnvironment;
import bergdb.nanotest.T;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.TestClock;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.NullStream;


/**
 * Simpler version of Concurrency.
 * 
 * @author Frans Lundberg
 */
public class Concurrency2 {
    private final Db db;
    private volatile boolean stop = false;
    private volatile long writeCount = 0;
    private volatile long errorCount = 0;
    private volatile long readCount = 0;
    private volatile Exception exception = null;
    
    public Concurrency2() {
        AppendOnlyStream stream = new NullStream();
        db = Db.builder().clock(new TestClock()).retainForever().noEvict().mainStream(stream).start();
    }
    
    /**
     * 
     * @param collector
     * @param seconds  Number of seconds to run the test.
     * @throws Exception
     */
    public void go(TestEnvironment collector, int seconds) throws Exception {
        Thread writer = new Thread(new Runnable() {
            public void run() {
                writer();
            }
        });
        writer.setName("writer");
        
        Thread reader = new Thread(new Runnable() {
            public void run() {
                reader();
            }
        });
        reader.setName("reader");
        
        db.execute(db.trans().put("0", "0").build());

        reader.start();
        writer.start();
        
        collector.report("note", "Runs one writer and one reader thread modifying the " +
        		"single key '0' in the database.");
        
        try {
            for (int i = 0; i < seconds; i++) {
                Thread.sleep(1000);
                collector.out().println("i = " + i + ", trans count: " + this.writeCount);
                if (this.exception != null) {
                    break;
                }
            }
        } finally {
            stop = true;
            reader.join();
            writer.join();
        }
        
        if (this.exception != null) {
            throw exception;
        }
    }
    
    private void writer() {
        while (!stop) {
            db.execute(db.trans().put("0", "1").build());
            this.writeCount++;
        }
    }
    
    private void reader() {
        while (!stop) {
            GetData gd = db.newGetData();
            byte[] value = db.getOne(Long.MAX_VALUE, Keys.toSegments("0"), gd);
            readCount++;
            
            if (value == null) {
                byte[] value2 = db.getOne(gd.actualLookupTime, Keys.toSegments("0"), gd);
                this.errorCount++;
                
                System.out.println("---- ERROR: no value for key '0' ----");
                System.out.println("value2 = " + (value2 == null ? "null" : Util.toString(value2)));
                System.out.println("writeCount: " + this.writeCount);
                System.out.println("readCount: " + this.readCount);
                System.out.println("errorCount: " + this.errorCount);
                
                this.exception = new RuntimeException("ERROR, no value for key '0'");
            }
        }
    }
    
    @T("f")
    public static void test1(TestEnvironment c) throws Exception {
        new Concurrency2().go(c, 10);
    }
    
    public static void main(String[] args) throws Throwable {
        Concurrency2 c = new Concurrency2();
        c.go(new BasicTestEnvironment(), 100);
    }
}
