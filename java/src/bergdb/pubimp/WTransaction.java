package bergdb.pubimp;

import bergdb.common.Bug;
import bergdb.core.RerunException;
import bergdb.core.Trans;
import bergdb.pub.Time;
import bergdb.pub.Transaction;
import bergdb.pub.util.SyncLevel;

class WTransaction implements Transaction {
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
        // A put or a delete at an object key, of any value, keeps the directory's indexes
        // (bergdb 020-10, section 5.1; 015-46): the transaction has a read time and the
        // directory's hash, so it runs as an rw() does, and may run again after a conflict.
        if (env.getObjectOpsSize() > 0) {
            trans = RwTransaction.executeRw(env, connection, null);
            connection.lastSposOfLastTrans = trans.lastPos;
        } else {
            trans = env.createTrans(connection.getDb());
            try {
                connection.getDb().execute(trans);
                connection.lastSposOfLastTrans = trans.lastPos;
            } catch (RerunException e) {
                throw new Bug("should not happen, no objectOps");
            }
        }
        
        return this;
    }
    
    /**
     * A w-transaction has no action and no outputs: null for every name.
     */
    public final <TYPE> TYPE getOutput(String name, Class<TYPE> clazz) {
        return RwTransaction.getOutput(null, name, clazz);
    }
    
    public Time getTime() {
        return Time.units(trans.tt);
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
        connection.getDb().sync(trans.lastPos, SyncLevel.ORDINARY);
    }
    
    /**
     * Waits for this transaction, as sync() does (2026-10-25, bergdb 005-45): it waited for
     * the database's last transaction.
     * 
     * @throws StreamIoException
     */
    public void sync(SyncLevel syncLevel) {
        connection.getDb().sync(trans.lastPos, syncLevel);
    }
}
