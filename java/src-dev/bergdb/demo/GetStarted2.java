package bergdb.demo;
import bergdb.pub.*;

public class GetStarted2 {
    public static void main(String[] args) throws java.io.IOException {
        Person adam = new Person("Adam");
        Person eve = new Person("Eve");
        try (Database db = Factory.database().create("db-GetStarted2").start()) {
            Connection c = db.connection();
            
            c.w().put("/genesis/a", adam)
                 .put("/genesis/e", eve).execute();
            
            System.out.println(c.get("/genesis/a", Person.class).name);
            System.out.println(c.get("/genesis/e", Person.class).name);
            c.sync();
        }
    }
}

/*
Demo class, GetStarted2.
*/