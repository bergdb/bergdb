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
Note, pub refers to the implementation package bergdb.pubimp in two places only:
[new DatabaseBuilderImp();] here, and Time's use of pubimp's TimeResolver (bergdb 005-56).
*/
