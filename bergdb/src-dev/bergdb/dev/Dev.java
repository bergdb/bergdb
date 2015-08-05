package bergdb.dev;

// TODO D. "File closed". I get stack traces like below for Interactive, addCards -n 1000000.

/*
Exception in thread "main" bergdb.storage.StreamIoException: File closed, /a/db-temp/00000000000250.bergdb.
    at bergdb.storage.RecoverableStream.read(RecoverableStream.java:336)
    at bergdb.core.NodeStream.readNode(NodeStream.java:173)
    at bergdb.dag.Dag.followPointer(Dag.java:360)
    at bergdb.dag.Dag.getEqNodeInSegment(Dag.java:490)
    at bergdb.dag.Dag.getOne(Dag.java:414)
    at bergdb.core.Db.getOneInternal(Db.java:921)
    at bergdb.core.Db.warmup(Db.java:1273)
    at bergdb.core.Db.executeInner(Db.java:1143)
    at bergdb.core.Db.execute(Db.java:1113)
    at bergdb.pubimp.RwTransaction.executeRw(RwTransaction.java:98)
    at bergdb.pubimp.WTransaction.execute(WTransaction.java:29)
    at bergdb.pubimp.WBuilderImp.execute(WBuilderImp.java:55)
    at bergdb.test.manual.Interactive.addCardsIfNeeded(Interactive.java:327)
    at bergdb.test.manual.Interactive.runAddCards(Interactive.java:249)
    at bergdb.test.manual.Interactive.runCommand(Interactive.java:106)
    at bergdb.test.manual.Interactive.runInteractively(Interactive.java:93)
    at bergdb.test.manual.Interactive.go(Interactive.java:57)
    at bergdb.test.manual.Interactive.main(Interactive.java:363)
Caused by: java.io.IOException: File closed, /a/db-temp/00000000000250.bergdb.
    at bergdb.stream.FileStream$DbFile.read(Unknown Source)
    at bergdb.stream.FileStream.read(Unknown Source)
    at bergdb.storage.BufferedStream.read(BufferedStream.java:294)
    at bergdb.storage.StorageManager.read(StorageManager.java:687)
 */

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
