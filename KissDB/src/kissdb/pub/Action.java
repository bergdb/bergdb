package kissdb.pub;

/**
 * An rw-transaction (read-write transaction) needs an implementation of Action to execute.
 * 
 * @author Frans Lundberg
 */
public interface Action {
    /**
     * Runs the database changes by reading from the database and 
     * writing values to it that depends on the the values read.
     * This method may run more than once if the read data was modified
     * by someone else after being read by this method and before 
     * the modifications were applied.
     * This method is the core of the STM approach (software transactional
     * memories) to attaining isolation of transactions.
     */
    public void run(RwEnvironment env);
}
