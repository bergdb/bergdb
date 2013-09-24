package bergdb.test.night;

import java.io.IOException;
import java.io.PrintStream;

import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
import bergdb.nanotest.TestCollector;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.WBuilder;
import bergdb.pubimp.DatabaseBuilderImp;
import bergdb.stream.MemoryStream;

/**
 * <p>A 'night' test. Creates 1.5M Accounts. 
 * Tests that all are there when database restarted. 
 * This test demonstrates a bug detected by Frans 130924.</p>
 * 
 * @author Frans Lundberg
 */
public class PayTest {
    
    /**
     * Runs that test. Requires 500 MB of RAM or so. 130924 Frans: Runs on 20 s on Cissi.
     * 
     * @author Frans Lundberg
     * @throws IOException 
     */
    @T("night")
    public static void testIt(TestCollector c) throws IOException {
        new PayTest().new Create().go(c);
    }
    
    private final long total = 1500 * 1000;
    private PrintStream out = System.out;
    
    private static String accountKey(long id) {
        StringBuilder b = new StringBuilder("/accounts/");
        String idString = "" + id;
        int zeros = 8 - idString.length();
        for (int i = 0; i < zeros; i++) {
            b.append('0');
        }
        b.append(idString);
        b.append(".obj");
        return b.toString();
    }
    
    public class Create {
        public void go(bergdb.nanotest.TestCollector coll) throws IOException {       
            PayTest.this.out = coll.out();
            
            MemoryStream mem = new MemoryStream();
            DatabaseBuilderImp b = (DatabaseBuilderImp) Factory.database();
            b.stream("main", mem);
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
                
                builder.build().execute();
                
                if ((i + 1) % 500 == 0) {
                    double progress = (100.0 * i) / (batchCount - 1);
                    out.printf("Progress: %.1f. Accounts: %d.\n", progress, (i + 1) * batchSize);
                }
            }
            
            database.sync();
            t0 = System.nanoTime() - t0;
            
            double time = 1e-9 * t0;
            out.printf("Total create time: %.1f s, time per account: %.6f s.\n", time, time / total);
            
            
            // ---- Iterate based on memory stream ----
            
            MemoryStream mem2 = mem.copy();
            mem = null;
            System.gc();
            
            b = (DatabaseBuilderImp) Factory.database();
            b.stream("main", mem2);
            database = b.start();
            c = database.connection();
            
            out.println("Now iterating the accounts of the restarted database.");
            
            t0 = System.nanoTime();
            long sum = 0;
            long count = 0;
            
            for (Account a : c.usePrimary(Account.class).dir("/accounts/").objects()) {
                String expectedKey = accountKey(count);
                
                if (!a.key.equals(expectedKey)) {
                    throw new AssertionError("Unexpected key: " + a.key + ", expected: " + expectedKey);
                }
                
                sum += a.balance;
                count += 1;
                
                if (count % 500000 == 0) {
                    out.printf("Iterated %.1fM accounts.\n", (count / 1e6));
                }
            }
            
            Assert.assertEquals(count, total);
            Assert.assertEquals(sum, total);
        }
    }
    
    /**
     * Simple payment class. For direct db storage.
     */
    public static class Payment {
        public long from;
        public long to;
        public long amount;
        public String message;
    }
    
    /**
     * Simple account class. For direct db storage.
     */
    public static class Account {
        public String key;
        public long balance;
    }
}
