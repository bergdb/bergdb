package bergdb.demo;
import bergdb.pub.*;

/**
 * Demonstrates historic queries.
 * 
 * @author Frans Lundberg
 */
public class GetStarted5 {
    public static void main(String[] args) throws java.io.IOException {
        Database db = Factory.database().dir("db-GetStarted5").start();
        Connection c = db.connection();
        
        c.put("/key", "a");
        Time time = db.currentTime();
        
        c.put("/key", "b");
        
        c.setLookupTime(time);
        String s = c.get("/key", String.class);
        
        System.out.println("s: " + s);
    }
}
