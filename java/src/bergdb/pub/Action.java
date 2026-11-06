package bergdb.pub;

/**
 * An rw-transaction (read-write transaction) needs an implementation of Action to execute.
 * 
 * @author Frans Lundberg
 */
public interface Action {
    /**
     * Runs the database changes by reading from the database and 
     * writing values to it that depends on the values read.
     * This method may run more than once if the read data was modified
     * by someone else after being read by this method and before 
     * the modifications were applied.
     * Its reads read the latest state as of its first read, not the transaction's
     * own puts and deletes (RwEnvironment.get()).
     * This method is the core of the STM approach (software transactional
     * memories) to attaining isolation of transactions.
     * Results for the caller go through outputs (RwEnvironment.setOutput()):
     * the caller gets those of the run that committed (Transaction.getOutput()).
     */
    public void run(RwEnvironment env);
}
