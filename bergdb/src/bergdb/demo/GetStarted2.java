package bergdb.demo;
import bergdb.pub.*;

/**
 * Demo class, GetStarted2.
 * 
 * @author Frans Lundberg
 */
public class GetStarted2 {
    public static void main(String[] args) throws java.io.IOException {
        Person adam = new Person("Adam");
        Person eve = new Person("Eve");
        Database db = Factory.database().dir("db-GetStarted2").start();
        Connection c = db.connection();
        
        c.w().put("/genesis/a.obj", adam)
             .put("/genesis/e.obj", eve).execute();
        
        System.out.println(c.get("/genesis/a.obj", Person.class).name);
        System.out.println(c.get("/genesis/e.obj", Person.class).name);
        db.sync();
    }
}
