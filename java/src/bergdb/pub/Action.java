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
     * If this method throws a RuntimeException, or any other Throwable that is not an Error,
     * such as a checked exception thrown without a declaration, nothing is written, rw()
     * throws it as it is, and the database goes on; an Error fails the database (Database,
     * "Errors"; bergdb 020-24-11, U11-7).
     *
     * <p>The transaction is made of the reads and writes through env only. A call of a
     * Connection, this one or another, or of the Database inside this method, such as a
     * put(), a w().execute(), a nested rw(), or an index's creation or deletion, is a
     * transaction of its own: it is committed when the call returns, it is not undone when
     * this method throws or runs again, and it is made again at each run. One that writes a
     * key that this method read through env, or the indexes of a directory that it writes
     * through env, conflicts with the transaction: this method runs again, makes the call
     * again, and conflicts again, so rw() does not return until the thread is interrupted
     * or the database stops (Connection.rw(); bergdb 020-24-11, U11-4). So write through
     * env, and read through env the state that the writes depend on.</p>
     *
     * <p>The environment may be used by several threads while this method runs; it is
     * closed when this method returns or throws (RwEnvironment).</p>
     */
    public void run(RwEnvironment env);
}
