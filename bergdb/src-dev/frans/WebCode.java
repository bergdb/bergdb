package frans;

import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.Time;

/**
 * Code snippets that are shown on www.bergdb.com.
 * Sync with bergdb/www/in/index.html.
 * 
 * @author Frans Lundberg
 */
public class WebCode {
    void m1() {
        System.out.println("== m1() ==");
        
        Person adam = new Person("Adam");
        
        Database database = Factory.database().dir("db1").start();
        Connection c = database.connection();
        c.put("/adam", adam);
        
        Person adam2 = c.get("/adam", Person.class);
        
        System.out.println("adam2 = " + adam2.name);
    }
    
    void m2() {
        System.out.println("== m2() ==");
        Person adam = new Person("Adam");
        Person eve = new Person("Eve");
        Database database = Factory.database().dir("db2").start();
        Connection c = database.connection();
        
        c.w().put("/adam", adam)
             .put("/eve", eve)
             .execute();
        
        System.out.println("adam: " + c.get("/adam", Person.class));
        System.out.println("eve: " + c.get("/eve", Person.class));
        
        byte[] data = new byte[]{1, 2, 3};
        String text = "my text";
        c.put("/data", data);
        c.put("/text", text);
        
        System.out.println("/data length: " + c.get("/data", byte[].class).length);
        System.out.println("/text: " + c.get("/text", String.class));
    }
    
    void m3() {
        // TODO A. Maybe c.getTime() is nicer?
        // TODO Consider Database.getTime() vs Database.time().
        
        System.out.println("== m3() ==");
        Database database = Factory.database().dir("db2").start();
        Connection c = database.connection();
        
        c.put("/key", "v1");
        Time t1 = database.getTime();
        c.put("/key", "v2");
        Time t2 = database.getTime();
        c.put("/key", "v3");
        Time t3 = database.getTime();
        
        c.setLookupTime(t1);
        String v1 = c.get("/key", String.class);    // returns "v1"
        c.setLookupTime(t2);
        String v2 = c.get("/key", String.class);    // returns "v2"
        c.setLookupTime(t3);
        String v3 = c.get("/key", String.class);    // returns "v3"
        
        System.out.println("v1 = " + v1);
        System.out.println("v2 = " + v2);
        System.out.println("v3 = " + v3);
        System.out.println("t1 = " + t1);
        System.out.println("t2 = " + t2);
        System.out.println("t3 = " + t3);
    }
    
    static class Person {
        String name;
        Person() {}
        Person(String name) { this.name = name; }
        public String toString() { return name; }
    }
    
    public static void main(String[] args) {
        WebCode w = new WebCode();
        w.m1();
        w.m2();
        w.m3();
    }
}
