package bergdb.demo;
import bergdb.pub.*;

class Person {
    public String name;
    public Person() {};
    public Person(String name) { this.name = name; }
}

public class GetStarted1 {
    public static void main(String[] args) throws java.io.IOException {
        Person adam = new Person("Adam");
        Database db = Factory.database().dir("db-GetStarted1").start();
        Connection c = db.connection();
        
        c.put("/p", adam);
        Person p = c.get("/p", Person.class);
        
        System.out.println(p.name);
        c.sync();
    }
}

/*
Demo class, GetStarted1.

@author  Frans Lundberg
*/
