package bergdb.demo;

import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;

// Example code:
// A complete program to put/get/delete a string under the name (key) "/a".
class Demo {
    private static void put() {
        Connection c = createDatabase();
        c.put("/a", "value");
        c.sync();
    }
    
    private static void get() {
        Connection c = createDatabase();
        System.out.println(c.get("/a", String.class));
    }

    private static void delete() {
        Connection c = createDatabase();
        c.delete("/a");
        c.sync();        
    }
    
    private static Connection createDatabase() {
        Database database = Factory.database().create("db-demo").start();
        return database.connection();
    }
    
    public static void main(String[] args) {
        if (args.length == 0) {
            System.out.println("Use one of: put, get, delete.");
            return;
        }
        
        if (args[0].equals("put")) {
            put();
        } else if (args[0].equals("get")) {
            get();
        } else if (args[0].equals("delete")) {
            delete();
        } else {
            System.out.println("Bad command.");
        }
    }
}

/*

Example is used in overview-pub.html. Included in Javadoc for Pub API.

*/