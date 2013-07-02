package bergdb.pub;

import bergdb.pubimp.DatabaseBuilderImp;

/**
 * The static method Factory.database() is used to create a DatabaseBuilder which in turn is 
 * used to create a Database.
 */
public final class Factory {
    /**
     * Creates a new builder object that is used to create a Database.
     */
    public static DatabaseBuilder database() {
        return new DatabaseBuilderImp();
    }
    
    /**
     * Useful for testing, prints hello message to System.out.
     */
    public static void printHello() {
        System.out.println("Hello from com.bergdb.pub.Factory.");
    }
}

/*
Note, the code [new DatabaseBuilderImp();] is the *only* reference to the implementation package
bergdb.pubimp.
*/
