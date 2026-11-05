package bergdb.test.manual;

import java.io.IOException;

import bergdb.pub.*;

/**
 * Executable class that creates an empty database and prints the size of the 
 * storage used.
 * 
 * @author Frans Lundberg
 */
public class StorageOverhead {
    public static void main(String[] args) throws IOException {
        Database d = Factory.database().create("temp-1").start();
        d.connection().w().put("/key", "value").execute();
        d.sync();
    }
}
