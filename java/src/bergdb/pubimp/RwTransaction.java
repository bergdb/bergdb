package bergdb.pubimp;

import java.util.HashMap;
import java.util.Map;

import bergdb.core.InternalDataException;
import bergdb.core.RerunException;
import bergdb.core.SyncLevel;
import bergdb.core.Trans;
import bergdb.pub.Action;
import bergdb.pub.Time;
import bergdb.pub.Transaction;
import bergdb.pub.util.DbException;
import bergdb.storage.StreamFormatException;
import bergdb.storage.StreamIoException;


public class RwTransaction implements Transaction {
    private ConnectionImp connection;
    private Action action;
    private int runCount;
    private HashMap<String, Object> output;
    private Trans trans;   // Core Layer transaction
    
    public RwTransaction(ConnectionImp connection, Action action) {
        assert action != null;
        assert connection != null;
        this.connection = connection;
        this.action = action;
        this.runCount = 0;
        this.output = null;
    }
    
    public int getRunCount() {
        return runCount;
    }
    
    public <TYPE> TYPE getOutput(String name, Class<TYPE> clazz) {
        return getOutput(output, name, clazz);
    }
    
    /**
     * Transaction.getOutput() given the outputs, null if there are none.
     * WTransaction uses it too, with null.
     * 
     * @throws IllegalArgumentException
     * @throws ClassCastException
     */
    static <TYPE> TYPE getOutput(Map<String, Object> output, String name, Class<TYPE> clazz) {
        RwEnvironmentImp.checkOutputName(name);
        
        if (clazz == null) {
            throw new IllegalArgumentException("clazz == null not allowed");
        }
        
        Object value = output == null ? null : output.get(name);
        if (value == null) {
            return null;
        }
        
        if (!clazz.isInstance(value)) {
            throw new ClassCastException("The output '" + name + "' is a " 
                    + value.getClass().getName() + ", not a " + clazz.getName() + ".");
        }
        
        return clazz.cast(value);
    }
    
    public Time getTime() {
        return Time.units(trans.tt);
    }
    
    /**
     * @throws StreamIoException
     * @throws StreamFormatException
     * @throws InternalDataException
     */
    public Transaction execute() 
            throws StreamFormatException, StreamIoException, InternalDataException {
        assert action != null;
        RwEnvironmentImp env = new RwEnvironmentImp(connection);
        try {
            this.trans = executeRw(env, connection, this);
        } finally {
            env.close();        // Valid only while the action runs (bergdb 005-12).
        }
        connection.lastSposOfLastTrans = trans.lastPos;
        return this;
    }

    /**
     * Internal method that executes a transaction.
     * Both RwTransactions and WTransactions uses this method.
     * 
     * @throws StreamIoException
     * @throws StreamFormatException
     * @throws InternalDataException
     */
    public static Trans executeRw(RwEnvironmentImp env, ConnectionImp connection, RwTransaction rw) {
        long sleepTime = 10;
        final IndexManager m = connection.getDatabaseImp().getIndexManager();
        int runCount = 0;
        Trans trans;
        
        while (true) {
            runCount++;
            if (rw != null) {
                rw.action.run(env);                     // User reads are done here, writes are requested.
            }
            env.indexEntries(m);                        // Internal reads are done here, internal writes are requested.
            trans = env.createTrans(connection.getDb());
            
            try {
                connection.getDb().execute(trans);      // Writes are executed.
                break;
            } catch (RerunException e) {
                if (rw == null) {
                    env.prepareForWRerun();
                } else {
                    env.prepareForRWRerun();
                }
                env.clearOutput();
                
                try {
                    Thread.sleep(sleepTime);
                    if (sleepTime < 10*1000) {
                        sleepTime = sleepTime * 2;
                    }
                } catch (InterruptedException e1) {
                    // A refusal: the transaction was not run, and the database goes on. The
                    // interrupt flag is set again (2026-10-27, bergdb 005-46).
                    Thread.currentThread().interrupt();
                    throw new DbException("The transaction was not run: the thread was "
                            + "interrupted while it waited to run it again after a conflict.", e1);
                }
            }
        }
        
        if (rw != null) {
            rw.output = env.getOutputMap();
            rw.runCount = runCount;
        }
        
        return trans;
    }
    
    /**
     * Same as: sync(SyncLevel.ORDINARY).
     * 
     * @throws StreamIoException
     */
    public void sync() {
        sync(SyncLevel.ORDINARY);
    }
    
    /**
     * @throws StreamIoException
     */
    public void sync(SyncLevel syncLevel) {
        connection.getDb().sync(trans.lastPos, syncLevel);
    }
}
