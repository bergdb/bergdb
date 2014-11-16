package bergdb.test;

import java.io.IOException;

import bergdb.core.Db;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.nanotest.Assert;
import bergdb.nanotest.BasicCollector;
import bergdb.nanotest.T;
import bergdb.nanotest.TestCollector;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pubimp.PubKeys;

/**
 * This class contains a test to reproduce bug-130924-1 reported by Frans.
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
    
    private static final long total = 151;
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
        return b.toString();
    }
    
    public void go1(bergdb.nanotest.TestCollector coll) throws IOException {
        Database database = Factory.database().memory().start();
        Connection c = database.connection();
        
        long id = 0;
        
        for (int i = 0; i < total; i++) {
            Account a = new Account();
            a.balance = 1;
            String key = accountKey(id);
            id += 1;
            c.w().put(key, a).execute();
        }
        
        long sum = 0;
        long count = 0;
        
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
            String ikey = PubKeys.u2i(accountKey(id));
            id += 1;
            db.execute(db.trans().put(ikey, "v").build());
        }
        
        GetMany g = db.newGetMany();
        g.startKey = Keys.toSegments("/dacc/-");
        g.stopCondition = new GetMany.Prefix(Keys.toSegments("/dacc/-"));
        g.inclusive = false;
        db.getMany(g);
        long count = 0;
        
        for (Kvt kvt : g.result) {
            String expected = PubKeys.u2i(accountKey(count));
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

FAILED! bergdb.test.Bug130924.test1
java.lang.ArrayIndexOutOfBoundsException: 2
    at bergdb.core.GetMany$Chain.setup(GetMany.java:287)
    at bergdb.core.Db.getMany(Db.java:1344)
    at bergdb.pubimp.UseIndexBuilderImp$IndexIterator.getMany(UseIndexBuilderImp.java:592)
    at bergdb.pubimp.UseIndexBuilderImp$IndexIterator.hasNext(UseIndexBuilderImp.java:611)
    at bergdb.pubimp.UseIndexBuilderImp$1$1.hasNext(UseIndexBuilderImp.java:503)
    at bergdb.test.Bug130924.go1(Bug130924.java:83)

*/