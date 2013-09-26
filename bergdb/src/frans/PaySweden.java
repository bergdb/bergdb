package frans;

import java.io.IOException;
import java.util.Random;

import bergdb.common.Util;
import bergdb.pub.Action;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.RwEnvironment;
import bergdb.pub.WBuilder;
import bergdb.pubimp.DatabaseBuilderImp;
import bergdb.stream.MemoryStream;

/**
 * <p>Concrete example to test performance; imagine a payment system to handle all 
 * electronic payments needed in Sweden. 24/7, instant replication, security.
 * 10M accounts, 300 payments/year per accounts gives use 3G payments/year which 
 * is around 100 payments/s average. Assume peak load of 10*100 = 1000 payments/s
 * (this is reasonable).</p>
 * 
 * <p>We could implement this two ways, both from the pub layer (not optimized, 
 * object serialization, nice code) and using the low-level db layer (optimized, bunch-up by 
 * clients, multiple clients to use cores).</p>
 * 
 * @author Frans Lundberg
 */
public class PaySweden {
    private final long total = 1200 * 1000;
    
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
        
        // Slow, added 10-15% to "create".
        //return String.format(Locale.US, "/accounts/%08d.obj", id);
    }
    
    public class Create {
        public void go(String[] args) throws IOException {
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
                    
                    if (id < 4 || id >= total - 4) {
                        System.out.println("Create, key: " + key);
                    }
                }
                
                builder.build().execute();
                
                if ((i + 1) % 100 == 0) {
                    double progress = (100.0 * i) / (batchCount - 1);
                    System.out.printf("Progress: %.1f. Accounts: %d.\n", progress, (i + 1) * batchCount);
                }
            }
            
            database.sync();
            t0 = System.nanoTime() - t0;
            
            double time = 1e-9 * t0;
            System.out.printf("Total create time: %.1f s, time per account: %.6f s.\n", time, time / total);
            
            
            // ---- Iterates based on cached existing data ----
            
            System.out.println("-- Iterating the accounts");
            
            int count = 0;
            int sum = 0;
            c = database.connection();
            
            for (Account a : c.usePrimary(Account.class).dir("/accounts/").objects()) {
                String expectedKey = accountKey(count);
                
                if (!a.key.equals(expectedKey)) {
                    throw new AssertionError("Unexpected key: " + a.key + ", expected: " + expectedKey);
                }
                
                sum += a.balance;
                count += 1;
                
                if (count % 500000 == 0) {
                    System.out.printf("Iterated %.1fM accounts.\n", (count / 1e6));
                }
            }
            
            
            // ---- Iterates based on memory stream ----
            
            System.out.println("-- Iterating the accounts, re-read from stream");
            
            MemoryStream mem2 = mem.copy();
            mem = null;
            System.gc();
            
            b = (DatabaseBuilderImp) Factory.database();
            b.stream("main", mem2);
            database = b.start();
            c = database.connection();
            
            t0 = System.nanoTime();
            sum = 0;
            count = 0;
            
            for (Account a : c.usePrimary(Account.class).dir("/accounts/").objects()) {
                String expectedKey = accountKey(count);
                
                if (!a.key.equals(expectedKey)) {
                    throw new AssertionError("Unexpected key: " + a.key + ", expected: " + expectedKey);
                }
                
                sum += a.balance;
                count += 1;
                
                if (count % 500000 == 0) {
                    System.out.printf("Iterated %.1fM accounts.\n", (count / 1e6));
                }
            }
            
            time = 1e-9 * (System.nanoTime() - t0);
            System.out.printf("Iterate. sum: %d, count: %d. time: %.1f s, time/account: %.6f s.\n", 
                    sum, count, time, time / count);            
        }
    }
    
    public class Pay {
        Random random;
        
        Pay() {
            random = new Random();
        }
        
        Payment createPayment() {
            Payment p = new Payment();
            p.from = random.nextInt((int) total);
            p.to = random.nextInt((int) total);
            p.message = "invoice:2304870";
            return p;
        }
        
        void go(String[] args) throws IOException {
            Database database = Factory.database().dir("/a/data/pay-sweden").start();
            Connection c = database.connection();
            long count = 100*1000;
            long t0 = System.nanoTime();
            double time;
            
            c.setEnableKeyReplace(true);
            
            //database.indexBuilder("payments-from-to").type("string").dir("/payments/")
            //        .field("from").field("to").createFast();
            
            for (int i = 0; i < count; i++) {
                final Payment p = createPayment();
                
                c.rw(new Action() {
                    public void run(RwEnvironment env) {
                        Account a1 = env.get(accountKey(p.from), Account.class);
                        Account a2 = env.get(accountKey(p.to), Account.class);
                        
                        if (a1 == null) {
                            System.out.println("ERROR, could not find from-account: " + p.from + ".");
                            return;
                        }
                        
                        if (a2 == null) {
                            System.out.println("ERROR, could not find to-account: " + p.to + ".");
                            return;
                        }
                        
                        //System.out.println("Paying from " + a1.key + " to " + a2.key);
                        
                        a1.balance -= p.amount;
                        a2.balance += p.amount;
                        
                        env.set(a1);
                        env.set(a2);
                        env.set("/payments/${transactionTime}.obj", p);
                    }
                }).execute();
            }
            
            time = 1e-9 * (System.nanoTime() - t0);
            System.out.printf("Payments: %d, time: %.1f s, time/payment: %.6f s. Payments/s: %.1f.\n", 
                    count, time, time / count, count / time);
        }
    }
    
    /**
     * Iterates through whole database with an iterator on primary index.
     */
    public class Iterate {
        public void go(String[] args) throws IOException {
            Database database = Factory.database().dir("/a/data/pay-sweden").start();
            Connection c = database.connection();
            long sum = 0;
            long count = 0;
            long t0 = System.nanoTime();
            
            for (Account a : c.usePrimary(Account.class).dir("/accounts/").objects()) {
                if (a == null) {
                    throw new AssertionError("a == null, never happens");
                }
                
                String expectedKey = accountKey(count);
                if (!a.key.equals(expectedKey)) {
                    throw new AssertionError("Got " + a.key + ", expected: " + expectedKey);
                }
                
                sum += a.balance;
                count += 1;
                
                if (count % 500000 == 0) {
                    System.out.printf("Iterated %.1fM accounts.\n", (count / 1e6));
                }
            }
            
            double time = 1e-9 * (System.nanoTime() - t0);
            
            System.out.printf("Iterate. sum: %d, count: %d. time: %.1f s, time/account: %.6f s.\n", 
                    sum, count, time, time / count);
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
    
    public static void help() {
        System.out.println("Choose one of: create / pay.");
    }
    
    public static void main(String[] args) throws IOException {
        if (args.length == 0) {
            help();
            return;
        }
        
        String first = args[0];
        String[] tail = Util.removeFirst(args);
        
        if (first.equals("create")) {
            new PaySweden().new Create().go(tail);
        } else if (first.equals("pay")) {
            new PaySweden().new Pay().go(tail);
        } else if (first.equals("iterate")) {
            new PaySweden().new Iterate().go(tail);
        } else {
            System.out.println("Error, bad first arg.");
            help();
        }
    }
}

/*

130924 Frans: Created the class. 
  On Cissi, it takes 100 s to create 10M Accounts. 2 GB in filesystem (200 bytes/account)
  Around 20 MB/s.
  CPU-bound. 0.000010 s per account (10 us).
  Iterate after create: takes 30 s, 3 us per account.

  For 1M accounts, doing 1M payments (with allocation, Random, everything) takes 44 s 
  (22 kpay/s). No indexing.
  For 1M accounts, doing 0.1M payments with everything including indexing on "from" and "to" 
  fields.
  
$ j bergdb.test.big.PaySweden iterate2
Iterate2: 0.5M accounts.
ERROR, missing account, i = 997000

$ j bergdb.test.big.PaySweden iterate
Iterated 0.5M accounts.
Exception in thread "main" java.lang.AssertionError: Got /accounts/01000000.obj, expected: /accounts/00997000.obj
    at bergdb.test.big.PaySweden$Iterate.go(PaySweden.java:192)
    at bergdb.test.big.PaySweden.main(PaySweden.java:283)

Reproduced it!

Trying with 1.5M instead of 10M...

Same result for "iterate":

$ j bergdb.test.big.PaySweden iterate
Iterated 0.5M accounts.
Exception in thread "main" java.lang.AssertionError: Got /accounts/01000000.obj, expected: /accounts/00997000.obj
    at bergdb.test.big.PaySweden$Iterate.go(PaySweden.java:191)
    at bergdb.test.big.PaySweden.main(PaySweden.java:282)

We are missing 3000 accounts!

*/