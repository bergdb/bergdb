package bergdb.test.night;

import java.io.IOException;
import java.io.PrintStream;

import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.WBuilder;
import bergdb.pubimp.DatabaseBuilderImp;
import bergdb.stream.MemoryStream;

/**
 * <p>A 'night' test. Creates 1.2M Accounts. 
 * Tests that all are there when database restarted. 
 * This test recreates a bug detected by Frans 130925.
 * Bug id: bug-130925.</p>
 * 
 * @author Frans Lundberg
 */
public class PayTest {
    
    /**
     * Runs that test. Requires 500 MB of RAM or so. 130925 Frans: Runs on 20 s on Cissi.
     * 
     * @throws IOException 
     */
    @T("night")
    public static void testIt(TestEnvironment c) throws IOException {
        new PayTest().new Create().go(c);
        System.gc();
    }
    
    private final long total = 1200 * 1000;
        // 1.0M or less does not reproduce the bug.
    private PrintStream out = System.out;
    
    private static String accountKey(long id) {
        StringBuilder b = new StringBuilder("/accounts/");
        String idString = "" + id;
        int zeros = 8 - idString.length();
        for (int i = 0; i < zeros; i++) {
            b.append('0');
        }
        b.append(idString);
        return b.toString();
    }
    
    public class Create {
        public void go(bergdb.nanotest.TestEnvironment coll) throws IOException {       
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
                    builder.put(key, a);
                    id += 1;
                }
                
                builder.execute();
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
     * Simple account class. For direct db storage.
     */
    public static class Account {
        public String key;
        public long balance;
    }
}
