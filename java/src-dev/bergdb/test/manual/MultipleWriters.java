package bergdb.test.manual;

import java.io.IOException;

import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;

/**
 * Code used to test what happens when multiple processes uses the same storage directory.
 * Run this class in multiple processes to test this.
 * 
 * @author Frans Lundberg
 */
public class MultipleWriters {
    public static void main(String[] args) throws IOException, InterruptedException {
        int n = 10;
        int runId = (int) (Math.random() * 1000);
        String id = "" + runId;
        
        Database d = Factory.database().dir("temp-MultipleWriters").start();
        Connection c = d.connection();
        System.out.println("Started run " + id + ".");
        
        for (int i = 0; i < n; i++) {
            String value = id + "-" + i;
            c.w().put("/k" + i, value).execute();
            System.out.println("Wrote value: " + value + ".");
            Thread.sleep(1000);
        }
        
        d.sync();
        d.stop();
        System.out.println(id + " done.");
    }
}
