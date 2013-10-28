package bergdb.pubimp;

import bergdb.common.Bug;
import bergdb.core.RerunException;
import bergdb.core.Trans;
import bergdb.pub.NoSuchObjectException;
import bergdb.pub.Transaction;

public class WTransaction implements Transaction {
    private ConnectionImp connection;
    private RwEnvironmentImp env;
    private int runCount = 0;
    private Trans trans;
    
    public WTransaction(RwEnvironmentImp env, ConnectionImp connection) {
        this.env = env;
        this.connection = connection;
    }
    
    /**
     * @throws StreamIoException
     * @throws StreamFormatException
     * @throws InternalDataException
     */
    public Transaction execute() {
        if (env.getObjectOpsSize() > 0) {
            trans = RwTransaction.executeRw(env, connection, null);
            connection.lastSposOfLastTrans = trans.lastSpos;
        } else {
            trans = env.createTrans();
            try {
                connection.getDb().execute(trans);
                connection.lastSposOfLastTrans = trans.lastSpos;
            } catch (RerunException e) {
                throw new Bug("should not happen, no objectOps");
            }
        }
        
        return this;
    }
    
    public final int getActionRunCount() {
        return runCount;
    }
    
    public final Object getOutput(String key) {
        if (key == null) {
            throw new IllegalArgumentException("key == null not allowed");
        }
        
        throw new NoSuchObjectException("No output objects for a WTransaction.");
    }
    
    /**
     * Not part of public API, exposes core transaction, core.Trans.
     * Use for debugging, testing.
     */
    public Trans getTrans() {
        return trans;
    }
    
    /**
     * @throws StreamIoException
     */
    public void sync() {
        connection.getDb().sync(trans.lastSpos);
    }
    
    /**
     * @throws StreamIoException
     */
    public void syncStrong() {
        connection.getDb().syncStrong(trans.lastSpos);
    }
}
