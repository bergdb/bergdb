package bergdb.demo;
import bergdb.pub.*;

/**
 * Demo class, makes a payment.
 * 
 * @author Frans Lundberg
 */
public class GetStarted4 {
    public static void main(String[] args) throws java.io.IOException {
        try (Database db = Factory.database().create("db-GetStarted4").start()) {
            Connection c = db.connection();
            
            Account a0 = c.get("/accounts/0", Account.class);
            Account a1 = c.get("/accounts/1", Account.class);
            
            // Creates accounts if they do not exist.
            
            if (a0 == null) {
                a0 = new Account("/accounts/0", 100);
                c.put(a0.key, a0);
            }
            
            if (a1 == null) {
                a1 = new Account("/accounts/1", 100);
                c.put(a1.key, a1);
            }
            
            // Performs a payment if there is enough money. The payer's new
            // balance is an output of the transaction: its result for the
            // caller.
            
            final long amount = 30;
            
            Transaction t = c.rw(new Action() {
                public void run(RwEnvironment env) {
                    Account acc0 = env.get("/accounts/0", Account.class);
                    Account acc1 = env.get("/accounts/1", Account.class);
                    
                    if (acc0.balance < amount) {
                        throw new IllegalStateException(
                                "Not enough money, account: " + acc0);
                    }
                    
                    acc0.balance -= amount;
                    acc1.balance += amount;
                    
                    env.put("/accounts/0", acc0);
                    env.put("/accounts/1", acc1);
                    env.setOutput("balance", acc0.balance);
                }
            });
            t.sync();
            
            System.out.println("Balance of /accounts/0 after the payment: " 
                    + t.getOutput("balance", Long.class));
            
            // Lists accounts
            
            for (Account a : c.usePrimary(Account.class).dir("/accounts/")
                    .objects()) {
                System.out.println(a);
            }
        }
    }
}
