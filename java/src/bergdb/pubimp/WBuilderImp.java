package bergdb.pubimp;

import bergdb.pub.Transaction;
import bergdb.pub.WBuilder;

/**
 * The WBuilder implementation.
 * A thin wrapper around RwEnvironmentImp.
 * 
 * <p>Its calls are synchronized (bergdb 021-22, 020-24-11, U11-6): a builder is for one
 * thread (Connection), but one that threads share takes their calls one at a time, so that
 * none is lost: a put() or delete() before execute() is in the transaction, and one after it,
 * also one that waited for it, throws IllegalStateException. Uncontended in the normal case.
 * Until 2026-11-09 the threads' puts broke the environment's HashMaps: some were lost, with
 * no error, or a thread spun in the map for as long as the JVM ran.</p>
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
    public synchronized WBuilder put(String ukey, Object object) {
        checkNotSpent("put");
        env.put(ukey, object);
        return this;
    }
    
    public synchronized WBuilder delete(String ukey) {
        checkNotSpent("delete");
        env.delete(ukey);
        return this;
    }
    
    /**
     * Spends the builder first, so that it is spent also when the transaction throws. A call
     * of the connection (ConnectionImp.enter(); bergdb 021-22): it runs a transaction on it.
     * 
     * @throws DbException if the database is faulty.
     * @throws IllegalStateException  If another thread is in a call of the connection; the
     *      builder is not spent then.
     */
    public synchronized Transaction execute() {
        checkNotSpent("execute");
        final boolean outer = connection.enter();
        try {
            spent = true;
            WTransaction t = new WTransaction(env, connection);
            t.execute();
            return t;
        } finally {
            connection.leave(outer);
        }
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
