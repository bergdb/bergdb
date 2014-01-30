package frans;

import bergdb.pub.*;

public class IndexDemo {
    static class Payment {
        String from;
        String to;
        long amount;
        
        public Payment() {}
        
        public Payment(String from, String to, long amount) {
            this.from = from;
            this.to = to;
            this.amount = amount;
        }
        
        public String toString() {
            return amount + " paid from " + from + " to " + to + ".";
        }
    }
    
    public static void main(String[] args) throws java.io.IOException {
        Database db = Factory.database().memory().start();
        Connection c = db.connection();
        
        db.indexBuilder("payment-from").type("string/unicode")
            .dir("/payments/").field("from")
            .createFast();
        
        c.w().put("/payments/1", new Payment("1001", "1002", 20))
             .put("/payments/2", new Payment("1002", "1009", 30))
             .put("/payments/3", new Payment("1000", "1009", 40))
             .execute();
        
        for (Payment p : c.useIndex("payment-from", Payment.class).objects()) {
            System.out.println(p);
        }
    }
}
