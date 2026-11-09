package frans;

import java.io.IOException;
import java.util.Random;

import bergdb.common.Util;
import bergdb.pub.Action;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.DatabaseBuilder;
import bergdb.pub.Factory;
import bergdb.pub.RwEnvironment;
import bergdb.pub.WBuilder;
import bergdb.pub.util.JobStatus;

/**
 * Pay demo, 1M accounts and a few actions: create, pay, iterate, random access.
 * Replication was used, until it was removed on 2026-11-04 (bergdb 005-11): the
 * database had a replica in /a/data/pay-demo-replica, added after each start.
 * 
 * <p>Three system properties make a smaller run, as java/before-commit.sh does (2026-11-09):
 * pay.accounts, the number of accounts, a multiple of 1000 (default 1000000); pay.count,
 * the payments of pay and the gets in each of access's ten rounds (default 100000); and
 * pay.dir, the database's directory (default /a/data/pay-demo). For example:
 * java -Dpay.accounts=2000 -Dpay.count=1000 -Dpay.dir=/tmp/pay -cp bergdb.jar frans.PayDemo create
 * </p>
 * 
 * @author Frans Lundberg
 */
public class PayDemo {
    private static final long n = Long.getLong("pay.accounts", 1*1000000);
    private static final int count = Integer.getInteger("pay.count", 100*1000);
    private static final String dir = System.getProperty("pay.dir", "/a/data/pay-demo");
    
    /** Creates database and starts it. */
    private static Database createDatabase() throws IOException {
        DatabaseBuilder builder = Factory.database().create(dir);
        
        long t0 = System.nanoTime();
        Database database = builder.start();
        double time = 1e-9 * (System.nanoTime() - t0);
        System.out.printf("Database started in %.1f s. Data dir: " + dir + "\n", time);
        
        return database;
    }
    
    private static String accountKey(long id) {
        StringBuilder b = new StringBuilder("/acc/");
        String idString = "" + id;
        int zeros = 8 - idString.length();
        for (int i = 0; i < zeros; i++) {
            b.append('0');
        }
        b.append(idString);
        return b.toString();
    }

    /** Creates the accounts and secondary indexes. */
    public void create(String[] args) throws IOException {
        Database database = createDatabase();
        Connection c = database.connection();
        long id = 0;
        long batchSize = 1000;
        long batchCount = n / batchSize;
        assert n % batchSize == 0;
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
            
            if ((i + 1) % 100 == 0) {
                System.out.printf("Accounts: %d.\n", (i + 1) * batchSize);
            }
        }
        
        // One level per field, each with its type (bergdb 020-10, section 3.1).
        JobStatus status = database.indexBuilder("payments-from-to")
                .dir("/payments/").type("long").field("from")
                .type("long").field("to").start().join();
        if (status.state() != JobStatus.State.ACTIVE) {
            throw new IllegalStateException("The index was not built: " + status);
        }
        
        database.sync();
        
        t0 = System.nanoTime() - t0;
        double time = 1e-9 * t0;
        System.out.printf("Total time: %.1f s, time/account: %.6f s.\n", time, time / n);        
    }

    /** Demonstrates payments. */
    public class Pay {
        Random random;
        
        Pay() {
            random = new Random();
        }
        
        /** A payment of 1 to 100 from one account to another. */
        Payment createPayment() {
            Payment p = new Payment();
            p.from = random.nextInt((int) n);
            
            // Another account: with to == from, the second put of go()'s rw would
            // win and create the amount.
            do {
                p.to = random.nextInt((int) n);
            } while (p.to == p.from);
            
            p.amount = 1 + random.nextInt(100);
            p.message = "invoice:2304870";
            return p;
        }
        
        void go(String[] args) throws IOException {
            Database database = createDatabase();
            Connection c = database.connection();
            double t0 = System.nanoTime();
            double time;
            
            c.setEnableKeyReplace(true);
            
            for (int i = 0; i < count; i++) {
                final Payment p = createPayment();
                
                c.rw(new Action() {
                    public void run(RwEnvironment env) {
                        String key1 = accountKey(p.from);
                        String key2 = accountKey(p.to);
                        
                        Account a1 = env.get(key1, Account.class);
                        Account a2 = env.get(key2, Account.class);
                        
                        a1.balance -= p.amount;
                        a2.balance += p.amount;
                        
                        env.put(key1, a1);
                        env.put(key2, a2);
                        env.put("/payments/${transactionTime}", p);
                    }
                });
                
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
    
    /** Iterates through database with iterator on primary index. */
    public void iter(String[] args) throws IOException {
        Database database = createDatabase();
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

    /** Demonstrates random access. */
    public void access() throws IOException {
        Random random = new Random();
        Database database = createDatabase();        
        Connection c = database.connection();
        
        for (int i = 0; i < 10; i++) {
            long t0 = System.nanoTime();
            
            for (int j = 0; j < count; j++) {
                int id = random.nextInt((int) n);
                Account a = c.get(accountKey(id), Account.class);
                assert a != null : "no account " + id;
            }
            
            double time = 1e-9 * (System.nanoTime() - t0);
            System.out.printf("Retrieved %d accounts, time: %.1f s. time/account: %.6f s.\n", count, time, time/count);
        }
    }
    
    /** Simple payment class. For direct db storage. */
    public static class Payment {
        public long from;
        public long to;
        public long amount;
        public String message;
    }
    
    /** Simple account class. For direct db storage. */
    public static class Account {
        public long balance;
    }
    
    public static void help() {
        System.out.println("One of: create / pay / iter / access.");
        System.out.println("Options: -Dpay.accounts=N (default 1000000, a multiple of 1000),");
        System.out.println("-Dpay.count=M (payments of pay, gets in each of access's ten rounds;");
        System.out.println("default 100000), -Dpay.dir=DIR (default /a/data/pay-demo).");
    }
    
    public static void main(String[] args) throws IOException {
        if (args.length == 0) {
            help();
            return;
        }
        
        String first = args[0];
        String[] tail = Util.removeFirst(args);
        PayDemo demo = new PayDemo();
        
        if (first.equals("create")) {
            demo.create(tail);
        } else if (first.equals("pay")) {
            demo.new Pay().go(tail);
        } else if (first.equals("iter")) {
            demo.iter(tail);
        } else if (first.equals("access")) {
            demo.access();
        } else {
            System.out.println("Error, bad first arg.");
            help();
        }
    }
}
