package bergdb.demo;

// A complete program to put/get/delete a string at the key "/a.txt".

import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;

class Demo {
    private static void put() {
        try (Database database = Factory.database().create("db-demo").start()) {
            Connection c = database.connection();
            c.put("/a.txt", "Hello world!");
            c.sync();
        }
    }

    private static void get() {
        try (Database database = Factory.database().open("db-demo").start()) {
            System.out.println(database.connection().get("/a.txt", String.class));
        }
    }

    private static void delete() {
        try (Database database = Factory.database().open("db-demo").start()) {
            Connection c = database.connection();
            c.delete("/a.txt");
            c.sync();
        }
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

The example of overview-pub.html, the Pub API's Javadoc overview ("A first
program"): the same code and output, with this package line added, as the
overview's Demo.java is in the default package, run as
"java -cp bergdb.jar Demo.java put". before-commit.sh runs this one as
bergdb.demo.Demo with put, get, delete and get, and checks its output. Keep
the two the same.

*/
