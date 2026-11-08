package bergdb.demo;

/**
 * An account of GetStarted4: a Data Object (bergdb 020-09, section 3), a public class with a
 * public no-argument constructor and public fields.
 */
public class Account {
    public String key;
    public long balance;
    
    public Account() {}
    
    public Account(String key, long balance) {
        this.key = key;
        this.balance = balance;
    }
    
    public String toString() {
        return key + ": " + balance;
    }
}
