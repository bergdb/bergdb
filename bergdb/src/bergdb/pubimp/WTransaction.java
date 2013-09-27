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
            trans = RwTransaction.executeRW(env, connection, null);
        } else {
            trans = env.createTrans();
            try {
                connection.getDb().execute(trans);
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
    public void waitForD1() {
        connection.getDb().waitForD1(trans.lastSpos);
    }
    
    /**
     * @throws StreamIoException
     */
    public void waitForD2() {
        connection.getDb().waitForD2(trans.lastSpos);
    }
}
