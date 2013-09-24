package bergdb.test;

import java.io.IOException;

import bergdb.core.Db;
import bergdb.core.GetMany;
import bergdb.core.Keys;
import bergdb.core.Kvt;
import bergdb.core.Trans;
import bergdb.nanotest.Assert;
import bergdb.nanotest.BasicCollector;
import bergdb.nanotest.T;
import bergdb.nanotest.TestCollector;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.stream.MemoryStream;

/**
 * This class contains a test to reproduce a bug found 2013-09-24 by Frans.
 * 
 * @author Frans Lundberg
 */
public class Bug130924 {
   
    @T("unit")
    public static void test1(TestCollector c) throws IOException {
        new Bug130924().go1(c);
    }
    
    @T("unit")
    public static void test2(TestCollector c) throws IOException {
        new Bug130924().go2(c);
    }
    
    private final long total = 151;
        // Test seems to fail for any total >= 151 and be successful for 
        // for total < 151.
    private static final String accountDir = "/acc/";
        // Another prefix, such as "/ac/" or "/acc1/" makes test successful.
    
    private String accountKey(long id) {
        StringBuilder b = new StringBuilder(accountDir);
        String idString = "" + id;
        int zeros = 8 - idString.length();
        for (int i = 0; i < zeros; i++) {
            b.append('0');
        }
        b.append(idString);
        b.append(".obj");
        return b.toString();
    }
    
    public void go1(bergdb.nanotest.TestCollector coll) throws IOException {
        Database database = Factory.database().memory().start();
        Connection c = database.connection();
        
        long id = 0;
        
        for (int i = 0; i < total; i++) {
            Account a = new Account();
            String key = accountKey(id);
            id += 1;
            c.w().set(key, a).execute();
        }
        
        long sum = 0;
        long count = 0;
        
        /*
        // The following code works:
        for (int i = 0; i < total; i++) {
            String key = accountKey(i);
            Account a = c.get(key, Account.class);
            if (a == null) {
                throw new AssertionError("Missing object for key: " + key);
            }
            
            sum += a.balance;
            count += 1;
        }*/
        
        for (Account a : c.usePrimary(Account.class).dir(accountDir).objects()) {
            sum += a.balance;
            count += 1;
        }
        
        Assert.assertEquals(count, total);
        Assert.assertEquals(sum, total);
    }
    
    /**
     * Low-level version of go1().
     */
    public void go2(bergdb.nanotest.TestCollector coll) throws IOException {
        Db db = Db.builder().testSetup().start();
        
        long id = 0;
        
        for (int i = 0; i < total; i++) {
            String key = accountKey(id);
            id += 1;
            db.execute(Trans.builder().set(key, "v"));
        }
        
        GetMany g = new GetMany();
        g.startKey = Keys.toSegments("/acc/");
        g.stopCondition = new GetMany.Prefix(Keys.toSegments("/acc/"));
        g.inclusive = false;
        db.getMany(g);
        long count = 0;
        
        for (Kvt kvt : g.result) {
            String expected = accountKey(count);
            Assert.assertEquals(expected, Keys.toString(kvt.key));
            count += 1;
        }
        
        Assert.assertEquals(count, total);
    }
    
    /**
     * Simple account class. For direct db storage.
     */
    public static class Account {
        public String key;
        public long balance;
    }
    
    public static void main(String[] args) throws Exception {
        BasicCollector c = new BasicCollector();
        c.setPrintOutput(true);
        c.setPrintStart(true);
        test1(c);
    }
}

/*

Typical stack trace:

FAILED! bergdb.test.Bug130924.testIt
java.lang.ArrayIndexOutOfBoundsException: 2
    at bergdb.core.GetMany$Chain.setup(GetMany.java:287)
    at bergdb.core.Db.getMany(Db.java:1344)
    at bergdb.pubimp.UseIndexBuilderImp$IndexIterator.getMany(UseIndexBuilderImp.java:592)
    at bergdb.pubimp.UseIndexBuilderImp$IndexIterator.hasNext(UseIndexBuilderImp.java:611)
    at bergdb.pubimp.UseIndexBuilderImp$1$1.hasNext(UseIndexBuilderImp.java:503)
    at bergdb.test.Bug130924$Create.go(Bug130924.java:89)
    at bergdb.test.Bug130924.testIt(Bug130924.java:25)


*/