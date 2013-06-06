package kissdb.pubimp;

import java.util.HashMap;

import kissdb.core.InternalDataException;
import kissdb.core.RerunException;
import kissdb.core.Trans;
import kissdb.pub.Action;
import kissdb.pub.NoSuchObjectException;
import kissdb.pub.Transaction;
import kissdb.storage.StreamFormatException;
import kissdb.storage.StreamIoException;


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
    
    public Object getOutput(String key) {
        if (key == null) {
            throw new IllegalArgumentException("key == null not allowed");
        }
        
        if (output == null) {
            throw new NoSuchObjectException("No output object named '" + key + "' exists.");
        }
        Object value = output.get(key);
        if (value == null) {
            throw new NoSuchObjectException("No output object named '" + key + "' exists.");
        }
        
        return value;
    }
    
    public String getOutputStream(String key) {
        return (String) getOutput(key);
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
        this.trans = executeRW(env, connection, this);
        return this;
    }

    /**
     * @throws StreamIoException
     * @throws StreamFormatException
     * @throws InternalDataException
     */
    public static Trans executeRW(RwEnvironmentImp env, ConnectionImp connection, RwTransaction rw) {
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
            trans = env.createTrans();
            
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
                    throw new RuntimeException(e1);
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
