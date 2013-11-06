package frans;

import bergdb.pub.*;

class Person {
    public String name;
    public Person() {};
    public Person(String name) { this.name = name; }
}

public class TimeDemo {
    public static void main(String[] args) throws java.io.IOException {
        TestClock clock = new TestClock();
        Database db = Factory.database().dir("db-TimeDemo").clock(clock).start();
        Connection c = db.connection();
        
        clock.setTime(100); c.put("/a", new Person("Adam"));
        clock.setTime(200); c.put("/e", new Person("Eve"));
        clock.setTime(300); c.put("/b", new Person("Bob"));
        
        // Prints: Adam, Bob, Eve
        for (Person p : c.usePrimary(Person.class).dir("/").objects()) {
            System.out.println(p.name);
        }
        
        c.setLookupTime(250); System.out.println("Lookup time: 250.");
        
        // Prints: Adam, Eve
        for (Person p : c.usePrimary(Person.class).dir("/").objects()) {
            System.out.println(p.name);
        }
    }
}
