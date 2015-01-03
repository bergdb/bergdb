package bergdb.dev;

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
