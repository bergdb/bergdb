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
public class PayDemo {
    private final long total = 1*1000000;
    private final String dir = "/a/data/pay-demo";
    
    
    private static String accountKey(long id) {
        StringBuilder b = new StringBuilder("/acc/");
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
        public void go(String[] args) throws IOException {
            Database database = Factory.database().dir(dir).start();
            
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
                
                if ((i + 1) % 100 == 0) {
                    double progress = (100.0 * i) / (batchCount - 1);
                    System.out.printf("Progress: %.1f. Accounts: %d.\n", progress, (i + 1) * batchCount);
                }
            }
            
            database.indexBuilder("payments-from-to").type("string").dir("/payments/")
                    .field("from").field("to").createFast();
            
            database.sync();
            t0 = System.nanoTime() - t0;
            
            double time = 1e-9 * t0;
            System.out.printf("Total create time: %.1f s, time per account: %.6f s.\n", time, time / total);
            
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
            Database database = Factory.database().dir(dir).build();
            
            long t0 = System.nanoTime();
            database.start();
            double time = 1e-9 * (System.nanoTime() - t0);
            System.out.printf("Started database in %.1f s.\n", time);
            
            Connection c = database.connection();
            long count = 100*1000;
            t0 = System.nanoTime();
            
            c.setEnableKeyReplace(true);
            
            for (int i = 0; i < count; i++) {
                final Payment p = createPayment();
                
                c.rw(new Action() {
                    public void run(RwEnvironment env) {
                        Account a1 = env.get(accountKey(p.from), Account.class);
                        Account a2 = env.get(accountKey(p.to), Account.class);
                        
                        a1.balance -= p.amount;
                        a2.balance += p.amount;
                        
                        env.set(a1);
                        env.set(a2);
                        env.set("/payments/${transactionTime}.obj", p);
                    }
                }).execute();
                
                if (i % 10000 == 0 && i > 0) {
                    time = 1e-9 * (System.nanoTime() - t0);
                    System.out.printf("time: %.1f s, time/payment: %.6f s. Payments/s: %.1f.\n", 
                            time, time / i, i / time);
                }
            }
            
            database.sync();
            
            time = 1e-9 * (System.nanoTime() - t0);
            System.out.printf("Payments: %d, time: %.1f s, time/payment: %.6f s. Payments/s: %.1f.\n", 
                    count, time, time / count, count / time);
        }
    }
    
    /**
     * Iterates through whole database with an iterator on primary index.
     */
    public class Iter {
        public void go(String[] args) throws IOException {
            Database database = Factory.database().dir(dir).start();
            Connection c = database.connection();
            
            for (int i = 0; i < 3; i++) {
                long t0 = System.nanoTime();
                long count = 0;
                long sum = 0;
                
                for (Account a : c.usePrimary(Account.class).dir("/acc/").objects()) {
                    if (a == null) {
                        throw new AssertionError("a == null, never happens");
                    }
                    
                    sum += a.balance;
                    count += 1;
                    
                    if (count % 200000 == 0) {
                        System.out.println("Count: " + count);
                    }
                }
                
                double time = 1e-9 * (System.nanoTime() - t0);
                
                System.out.printf("Iterate. sum: %d, count: %d. time: %.1f s, time/account: %.6f s.\n", 
                        sum, count, time, time / count);
            }
        }
    }
    
    /**
     * Demonstrates random access.
     * @throws IOException 
     */
    public void access() throws IOException {
        Random random = new Random();
        
        Database database = Factory.database().dir(dir).build();
        
        long t0 = System.nanoTime();
        database.start();
        double time = 1e-9 * (System.nanoTime() - t0);
        System.out.printf("Started database in %.1f s.\n", time);
        
        Connection c = database.connection();
        
        for (int i = 0; i < 10; i++) {
            t0 = System.nanoTime();
            
            for (int j = 0; j < 100*1000; j++) {
                int id = random.nextInt(1000*1000);
                c.get(accountKey(id), Account.class);
            }
            
            time = 1e-9 * (System.nanoTime() - t0);
            System.out.printf("Retrieved 100k accounts, time: %.1f s. time/account: %.6f s.\n", time, time/100000.0);
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
        System.out.println("One of: create / pay / iter / access.");
    }
    
    public static void main(String[] args) throws IOException {
        if (args.length == 0) {
            help();
            return;
        }
        
        String first = args[0];
        String[] tail = Util.removeFirst(args);
        
        if (first.equals("create")) {
            new PayDemo().new Create().go(tail);
        } else if (first.equals("pay")) {
            new PayDemo().new Pay().go(tail);
        } else if (first.equals("iter")) {
            new PayDemo().new Iter().go(tail);
        } else if (first.equals("access")) {
            new PayDemo().access();
        } else {
            System.out.println("Error, bad first arg.");
            help();
        }
    }
}

/*

*/