package bergdb.demo;
import bergdb.pub.*;

class Account {
    String key;
    long balance;
    
    Account() {}
    
    Account(String key, long balance) {
        this.key = key;
        this.balance = balance;
    }
    
    public String toString() {
        return key + ": " + balance;
    }
}

/**
 * Demo class, makes a payment.
 * 
 * @author Frans Lundberg
 */
public class GetStarted4 {
    public static void main(String[] args) throws java.io.IOException {
        Database db = Factory.database().dir("db-GetStarted4").start();
        Connection c = db.connection();
        
        Account a0 = c.get("/accounts/0.obj", Account.class);
        Account a1 = c.get("/accounts/1.obj", Account.class);
        
        // Creates accounts if they do not exist.
        
        if (a0 == null) {
            a0 = new Account("/accounts/0.obj", 100);
            c.w().set(a0).execute();
        }
        
        if (a1 == null) {
            a1 = new Account("/accounts/1.obj", 100);
            c.w().set(a1).execute();
        }
        
        // Performs a payment if there is enough money.
        
        final long amount = 30;
        
        c.rw(new Action() {
            public void run(RwEnvironment env) {
                Account acc0 = env.get("/accounts/0.obj", Account.class);
                Account acc1 = env.get("/accounts/1.obj", Account.class);
                
                if (acc0.balance < amount) {
                    throw new IllegalStateException(
                            "Not enough money, account: " + acc0);
                }
                
                acc0.balance -= amount;
                acc1.balance += amount;
                
                env.set(acc0);
                env.set(acc1);
            }
        }).execute();
        
        db.sync();
        
        // Lists accounts
        
        for (Account a : c.usePrimary(Account.class).objects()) {
            System.out.println(a);
        }
    }
}
