package frans;

import java.io.IOException;
import java.io.PrintStream;

import bergdb.core.NoEvictBoss;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
import bergdb.nanotest.TestCollector;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.Transaction;
import bergdb.pub.WBuilder;
import bergdb.pubimp.DatabaseBuilderImp;
import bergdb.stream.MemoryStream;

// TODO A. Fix this bug!

/**
 * Trying to fix bug-130925, see test.night.PayTest.
 * 
 * @author Frans Lundberg
 */
public class PayTestBugFix {
    
    /**
     * Runs that test. Requires 500 MB of RAM or so. 130925 Frans: Runs on 20 s on Cissi.
     * 
     * @author Frans Lundberg
     * @throws IOException 
     */
    @T("night")
    public static void testIt(TestCollector c) throws IOException {
        PayTestBugFix pt = new PayTestBugFix();
        pt.out = c.out();
        pt.go();
        System.gc();
    }
    
    private final long total = 1199000;
        // 1200k bug!
        // 1000k ok
        // 1001k ok
        // 1100k ok
        // 1150k ok
        // 1180k ok
        // 1199k   Unexpected key: /accounts/01000000.obj, expected: /accounts/00997000.obj
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
    
    public void go() throws IOException {
        MemoryStream mem = new MemoryStream();
        DatabaseBuilderImp b = (DatabaseBuilderImp) Factory.database();
        b.stream("main", mem);
        b.noReclaim();
        b.evictBoss(new NoEvictBoss());
        Database database = b.start();
        
        Connection c = database.connection();
        long id = 0;
        long batchSize = 1000;
        long batchCount = total / batchSize;
        assert total % batchSize == 0;
        long t0 = System.nanoTime();
        
        for (int i = 0; i < batchCount; i++) {
            WBuilder builder = c.w();
            
            for (int j = 0; j < batchSize; j++) {
                Account a = new Account();
                a.balance = 1;
                String key = accountKey(id);
                builder.set(key, a);
                id += 1;
            }
            
            Transaction t = builder.build().execute();
            
            //t.waitForD1();  //  <-- Does not work, even with this line.
            
            //if (id == 800*1000) {
            //    Trans trans = ((WTransaction) t).getTrans();
            //    System.out.println("Trans size: " + (trans.lastSpos - trans.spos));
                // Trans size is 197k bytes.
            //}
            
            if (id % 200000 == 0) {
                System.out.printf("Created %.0fk accounts.\n", id / 1000.0);
            }
        }
        
        database.sync();
        t0 = System.nanoTime() - t0;
        double time = 1e-9 * t0;
        out.printf("Total create time: %.1f s, time per account: %.6f s.\n", time, time / total);
        
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
        
        // -- Print a few
        
        out.println("---- A few accounts of interest: ");
        long[] ids = new long[] {
                0, 996998, 996999, 
                997000, 998000, 998500, 999000, 999999, 
                1000000, 1000001, 1000002, 1100000, 1199999
        };
        
        for (long theId : ids) {
            out.println(theId + ": " + c.get(accountKey(theId), Account.class));
        }
        
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
        }
        
        Assert.assertEquals(count, total);
        Assert.assertEquals(sum, total);
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
        new PayTestBugFix().go();
    }
}

/*

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

== 130927 ==
Idea: can it have to do with newly created nodes when we have splits?
Db.setKvs(). What happens to access paths when we have splits?
But new nodes are always added to transactionNodes and written to stream.

== 130926 ==
Hmmm, could something have to to with 20M startup distance. How large is a transaction, 
1000 KVs in one.

Hurray, something useful. this.startupDistance += 3*1000000 in Db.startInner()
fixes the issue. Some nodes seem to get too dirty, re-check logic for this.
Can it be tested / refactored?

*/