package kissdb.demo;
import kissdb.pub.*;

class Person {
    public String name;
    public Person() {};
    public Person(String name) { this.name = name; }
}

public class GetStarted1 {
    public static void main(String[] args) throws java.io.IOException {
        Person adam = new Person("Adam");
        Database db = Factory.database().dir("demo-db").start();
        Connection c = db.connection();
        c.w().set("p.obj", adam).execute();
        Person p = c.get("p.obj", Person.class);
        System.out.println(p.name);
        db.sync();
    }
}

/*

If we have special code for one-set and Connection.sync().

    Person adam = new Person("Adam");
    Person p;
    
    Connection c = Factory.database().dir("demo-db").start().connection();
    c.set("p.obj", adam);
    p = c.get("p.obj", Person.class);
    System.out.println(p.name);
    c.sync();

c.sync() makes sense, but we probably should have an explicit Database anyway.
    
    // One liner to store object.
    Factory.database().dir("demo-db").start().connection().w().set("p.obj", new Person("Adam").execute().sync();
    
    // With single-set method.
    Factory.database().dir("demo-db").start().connection().set("p.obj", new Person("Adam").sync();
*/