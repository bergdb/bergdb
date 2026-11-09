package bergdb.pubimp;

import bergdb.pub.Transaction;
import bergdb.pub.WBuilder;

/**
 * The WBuilder implementation.
 * A thin wrapper around RwEnvironmentImp.
 * 
 * @see bergdb.pub.WBuilder
 * @author Frans Lundberg
 */
class WBuilderImp implements WBuilder {
    private ConnectionImp connection;
    private RwEnvironmentImp env;
    private boolean spent;                  // execute() was called (bergdb 020-21, 2)
    
    public WBuilderImp(ConnectionImp connection) {
        assert connection != null;
        this.connection = connection;
        this.env = new RwEnvironmentImp(connection);
    }
    
    /**
     * @throws IllegalArgumentException  
     *      If 'key' is null or otherwise invalid, or if object is null.
     */
    public WBuilder put(String ukey, Object object) {
        checkNotSpent("put");
        env.put(ukey, object);
        return this;
    }
    
    public WBuilder delete(String ukey) {
        checkNotSpent("delete");
        env.delete(ukey);
        return this;
    }
    
    /**
     * Spends the builder first, so that it is spent also when the transaction throws.
     * 
     * @throws DbException if the database is faulty.
     */
    public Transaction execute() {
        checkNotSpent("execute");
        spent = true;
        WTransaction t = new WTransaction(env, connection);
        t.execute();
        return t;
    }
    
    /**
     * A builder is spent by execute(), as IndexBuilder by start() (bergdb 020-21, 2; 020-19,
     * Q2): until 2026-11-09 a second execute() ran the same writes again as a new
     * transaction, and a put() after execute() added to them.
     */
    private void checkNotSpent(String call) {
        if (spent) {
            throw new IllegalStateException(call + "() after execute(): the builder is spent; "
                    + "get a new one with Connection.w().");
        }
    }
}
