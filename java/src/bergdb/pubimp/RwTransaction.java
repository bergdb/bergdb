package bergdb.pubimp;

import java.util.HashMap;
import java.util.Map;

import bergdb.core.InternalDataException;
import bergdb.core.RerunException;
import bergdb.core.Trans;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.Action;
import bergdb.pub.Time;
import bergdb.pub.Transaction;
import bergdb.pub.util.DbException;
import bergdb.pub.util.SyncLevel;
import bergdb.storage.StreamFormatException;
import bergdb.storage.StreamIoException;


class RwTransaction implements Transaction {
    /** The sleep before the first rerun of a conflicting transaction, ms (bergdb 015-88). */
    static final long FIRST_SLEEP = 10;
    /** The longest sleep between reruns, ms (Frans, 2026-11-05, bergdb 015-88). */
    static final long MAX_SLEEP = 640;
    
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
     * @throws DbException
     */
    public static Trans executeRw(RwEnvironmentImp env, ConnectionImp connection, RwTransaction rw) {
        try {
            return executeRwInner(env, connection, rw);
        } catch (Error e) {
            // In the application's Action too, before the Core's execute (2026-11-06, bergdb
            // 019-10): the database fails, and the Error is thrown as it is.
            throw connection.failed(e);
        }
    }
    
    private static Trans executeRwInner(RwEnvironmentImp env, ConnectionImp connection,
            RwTransaction rw) {
        long sleepTime = FIRST_SLEEP;
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
                    sleepTime = nextSleep(sleepTime);
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
     * The sleep before the next rerun, given the last one: it doubles up to MAX_SLEEP,
     * so 10, 20, 40, 80, 160, 320, 640, 640, ... ms (bergdb 015-88).
     */
    static long nextSleep(long sleepTime) {
        return Math.min(sleepTime * 2, MAX_SLEEP);
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
    
    @Nano
    private static void testSleepsBetweenReruns() {
        long[] expected = {10, 20, 40, 80, 160, 320, 640, 640};
        long sleepTime = FIRST_SLEEP;
        for (int i = 0; i < expected.length; i++) {
            Assert.assertEquals("sleep " + i, expected[i], sleepTime);
            sleepTime = nextSleep(sleepTime);
        }
    }
}
