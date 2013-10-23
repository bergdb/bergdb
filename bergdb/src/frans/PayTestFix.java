package frans;

import java.io.IOException;
import java.io.PrintStream;

import bergdb.core.Db;
import bergdb.core.NoEvictBoss;
import bergdb.graph.GetData;
import bergdb.graph.Graph;
import bergdb.graph.INode;
import bergdb.graph.KeyNode;
import bergdb.graph.Keys;
import bergdb.graph.TopNode;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
import bergdb.nanotest.TestCollector;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.TestClock;
import bergdb.pub.Transaction;
import bergdb.pub.WBuilder;
import bergdb.pubimp.DatabaseBuilderImp;
import bergdb.pubimp.DatabaseImp;
import bergdb.pubimp.PubKeys;
import bergdb.stream.MemoryStream;

/**
 * Trying to fix bug-130925, see test.night.PayTest.
 * 
 * @author Frans Lundberg
 */
public class PayTestFix {
    
    /**
     * Runs that test. Requires 500 MB of RAM or so. 130925 Frans: Runs on 20 s on Cissi.
     *
     * @throws IOException 
     */
    @T("night")
    public static void testIt(TestCollector c) throws IOException {
        PayTestFix pt = new PayTestFix();
        pt.out = c.out();
        pt.go();
        System.gc();
    }
    
    private final long total = 1200000;
    private final int batchSize = 1000; 
    //private final int batchSize = 1;  // Fails in similar way.

    //
    // total:
    // 1200k bug! Unexpected key: /accounts/01000000.obj, expected: /accounts/00997000.obj
    // 1000k ok
    // 1001k ok
    // 1100k ok
    // 1150k ok
    // 1180k ok
    // 1199k Unexpected key: /accounts/01000000.obj, expected: /accounts/00997000.obj
    //
    
    private static final String dirName = "/accounts/";
        // Changing to /account/ makes code work.
     
    private PrintStream out = System.out;
    
    
    private static String accountKey(long id) {
        StringBuilder b = new StringBuilder(dirName);
        
        String idString = "" + id;
        int zeros = 8 - idString.length();
        for (int i = 0; i < zeros; i++) {
            b.append('0');
        }
        b.append(idString);
        b.append(".obj");
        return b.toString();
    }
    
    @SuppressWarnings("all")
    public void go() throws IOException {
        TestClock clock = new TestClock();
        MemoryStream mem = new MemoryStream();
        DatabaseBuilderImp b = (DatabaseBuilderImp) Factory.database();
        b.clock(clock);
        b.stream("main", mem);
        b.noReclaim();
        b.evictBoss(new NoEvictBoss());
        Database database = b.start();
        
        Connection c = database.connection();
        long id = 0;
        long batchCount = total / batchSize;
        assert total % batchSize == 0;
        long t0 = System.nanoTime();
        
        for (int i = 0; i < batchCount; i++) {
            WBuilder builder = c.w();
            
            for (int j = 0; j < batchSize; j++) {
                Account a = new Account();
                a.balance = 1;
                String key = accountKey(id);
                builder.put(key, a);
                id += 1;
            }
            
            clock.setTime(i == 0 ? 1 : i * batchSize);
            
            @SuppressWarnings("unused")
            Transaction t = builder.build().execute();
            //t.waitForD1();  //  <-- Does not work, even with this line.
            
            if (id % 200000 == 0) {
                System.out.printf("Created %.0fk accounts.\n", id / 1000.0);
            }
            
            if (id % 100000 == 0) {
                Db db = ((DatabaseImp) database).getDb();
                db.checkNodes();
            }
            
            if (id == 1000*1000) {
                printAccessPath(database, "0-just-written");
            }
        }
        
        database.sync();
        t0 = System.nanoTime() - t0;
        double time = 1e-9 * t0;
        out.printf("Total create time: %.1f s, time per account: %.6f s.\n", time, time / total);
        
        // ---- Prints access path to KV
        
        printAccessPath(database, "1");
        
        // ----
        
        out.println("---- Iterating the accounts, cached values.");
        c = database.connection();
        
        t0 = System.nanoTime();
        long count = 0;
        
        for (Account a : c.usePrimary(Account.class).dir(dirName).objects()) {
            String expectedKey = accountKey(count);
            
            if (!a.key.equals(expectedKey)) {
                throw new AssertionError("Unexpected key: " + a.key + ", expected: " + expectedKey);
            }
            
            count += 1;
            
            if (count % 200000 == 0) {
                out.printf("Iterated %.0fk accounts.\n", (count / 1000.0));
            }
        }
        
        Assert.assertEquals(count, total);
        
        
        
        // ---- Iterate based on memory stream ----
        
        MemoryStream mem2 = mem.copy();
        mem = null;
        System.gc();
        
        b = (DatabaseBuilderImp) Factory.database();
        b.stream("main", mem2);
        b.noReclaim();
        b.evictBoss(new NoEvictBoss());
        database = b.start();
        c = database.connection();
        
        
        Db db = ((DatabaseImp) database).getDb();
        db.checkNodes();
        
        
        // -- Prints a few
        
        printAccessPath(database, "2-restarted");
        
        out.println("---- Iterating the accounts of the restarted database.");
        
        t0 = System.nanoTime();
        long sum = 0;
        count = 0;
        
        for (Account a : c.usePrimary(Account.class).dir(dirName).objects()) {
            String expectedKey = accountKey(count);
            
            if (!a.key.equals(expectedKey)) {
                throw new AssertionError("Unexpected key: " + a.key + ", expected: " + expectedKey);
            }
            
            sum += a.balance;
            count += 1;
            
            if (count % 200000 == 0) {
                out.printf("Iterated %.0fk accounts.\n", (count / 1000.0));
            }
            
            if (count % 50000 == 0) {
                db.checkNodes();
            }
        }
        
        Assert.assertEquals(count, total);
        Assert.assertEquals(sum, total);
    }

    private void printAccessPath(Database database, String caseName) {
        //long[] theAccounts = new long[]{999999, 1000000};
        long[] theAccounts = new long[]{999999};
        
        Db dbTemp = (Db) ((DatabaseImp) database).getDb();
        GetData gd = dbTemp.newGetData();
        gd.pointerListener = new Graph.PointerListener() {
            public void superRootAccessed(TopNode superRoot) {
                System.out.println("Super root: " + superRoot);
            }
            
            public void pointerFollowed(INode predecessor, int pointerIndex, INode result, int pointerType) {
                System.out.println("Pointer followed, index " + pointerIndex + ", result: " + result);
                long id = result.getId();
                
                if (id == 159470936L || id == 222520040 || id == 226129416) {
                    System.out.print(((KeyNode) result).print("    "));
                }
            }
        };
        
        System.out.println("\n---- " + caseName + ": Printing pointers ----");
        System.out.println("Stream length: " + dbTemp.getStreamLength());
        
        for (int i = 0; i < theAccounts.length; i++) {
            String key = accountKey(theAccounts[i]);
            System.out.println("* key: " + key);
            byte[] value = dbTemp.getOne(Long.MAX_VALUE, Keys.toSegments(PubKeys.u2i(key)), gd);
            System.out.println("value = " + value);
        }
        
        dbTemp.getOne(Long.MAX_VALUE, Keys.toSegments(accountKey(990000)), gd);
        dbTemp.getOne(Long.MAX_VALUE, Keys.toSegments(accountKey(999000)), gd);
        System.out.println("Print done.");
    }
    
    /**
     * Simple account class. For direct db storage.
     */
    public static class Account {
        public String key;
        public long balance;
        public String toString() { return key + ": " + balance; }
    }
    
    public static void main(String[] args) throws IOException {
        new PayTestFix().go();
    }
}

/*

== 131007 ==

Tracing getOne() is interesting. Shows what seems to be inconsistencies!
Forward pointers exist, but not all ancestors to forward pointer have 
spos > pointee.spos - startupDist.

See bug-130925/notes.txt.


== 13092x ==

Bug-hunting notes.

7-byte pieces:

/daccou nts/
/daccou nts/-00 001111. obj     -- 

/daccou nts/-00 999999. obj     -- 
/daccou nts/-01 000000. obj     -- 


Expected:
/accounts/00997000.obj

Got:
/accounts/01000000.obj


Alternative:
/daccou nt/-000 99999.o bj    
/daccou nt/-001 00000.o bj     

== 130927 ==
Idea: can it have to do with newly created nodes when we have splits?
Db.setKvs(). What happens to access paths when we have splits?
But new nodes are always added to transactionNodes and written to stream.

== 130926 ==
Hmmm, could something have to to with 20M startup distance. How large is a transaction, 
1000 KVs in one.

Hurrah, something useful. this.startupDistance += 3*1000000 in Db.startInner()
fixes the issue. Some nodes seem to get too dirty, re-check logic for this.
Can it be tested / refactored?

*/