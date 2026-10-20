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
}

/*
Note, the code [new DatabaseBuilderImp();] is the *only* reference to the implementation package
bergdb.pubimp. Nice, ha!?
*/
