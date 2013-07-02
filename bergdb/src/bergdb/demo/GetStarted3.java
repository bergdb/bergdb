package bergdb.demo;
import bergdb.pub.*;

/**
 * Demo class, iterates the objects stored with GetStarted2.
 * 
 * @author Frans Lundberg
 */
public class GetStarted3 {
    public static void main(String[] args) throws java.io.IOException {
        Database db = Factory.database().dir("db-GetStarted2").start();
        Connection c = db.connection();
        
        for (Person p : c.usePrimary(Person.class).dir("/genesis/").objects()) {
            System.out.println(p.name);
        }
        
        System.out.println("Backward:");
        for (Person p : c.usePrimary(Person.class).dir("/genesis/").backward().objects()) {
            System.out.println(p.name);
        }
        
        System.out.println("Start at c:");
        for (Person p : c.usePrimary(Person.class).dir("/genesis/").startAt("c").objects()) {
            System.out.println(p.name);
        }
    }
}
