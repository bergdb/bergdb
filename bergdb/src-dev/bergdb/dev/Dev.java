package bergdb.dev;

//
// TODO Consider - email 150322 - indexing for "subfields".
// Looks like we could add support for changing mostly DbObject.getLong(String name) etc.
// Allow field name like "Date.timeInMillis" - a dot separates parts of field, allows getting subfield.
//
// TODO LATER Add support for JSON. Pub API and changes to DbObject, I guess.
// "Promised" to Stefan Edlich 150109.
//
// TODO LATER Consider calling Db.possiblyEvict() several times from getMany().
//  Proportional to number of KVs gotten? Does not seem fair to getOne() to just
//  call possiblyEvict for an operation that might retrieve 1000 KVs. The operation 
//  might cause a large increase of the cache size.
//

/**
 * Dummy test code; for development only.
 */
public class Dev {    
    public static void main(String[] args) throws Exception { 
        go();
    }
    
    public static void go() {
        String s = "a";
        
        assert (s = "b").equals("b");
        
        boolean assertsEnabled = false;
        assert (assertsEnabled = true) == true;
        
        System.out.println("s = " + s);
        System.out.println("assertsEnabled = " + assertsEnabled);
    }
}
