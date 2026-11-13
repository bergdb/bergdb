package bergdb.core;

/**
 * A transformation of a database value after DB.execute() has been called.
 * This allows us to, for example, do atomic increments of counters without adding them to
 * the read set.
 * 
 * @author Frans Lundberg
 */
public interface ValueTransformation {
    /**
     * Transform the value 'inputValue' to a new byte array as output. The previous value
     * for the key is available and may be used to compute the new value.
     * 
     * <p>It runs in Db.execute(), under the write lock, at the transaction's time, after the
     * key transformations and before the transaction's go point (Db.transformValues; bergdb
     * 026-06): the transformations of a transaction run one at a time, in the order of the
     * transaction's keys as the key transformations left them. The previous value is the one
     * before the transaction. It should be quick: other writers wait for the lock.</p>
     * 
     * <p>A transformation that throws a RuntimeException refuses the transaction with a
     * DbException whose cause is the exception; nothing of the transaction is written, and the
     * database goes on (bergdb 010-04, R5). Its result is checked as a value given directly:
     * a value of more than Db.MAX_VALUE_BYTES (8 MiB, L4), or keys and values of the
     * transaction of more than Db.MAX_TRANS_BYTES (32 MiB, L5), counted with the results,
     * refuse the transaction in the same way (Db, "Limits"). A refused transaction is left as
     * it was before the call: each KV with a value transformation has its value as given
     * again, so that the Trans can be run again. An Error, such as an OutOfMemoryError, fails
     * the database, as anywhere in a call (Db, "Errors"). Until bergdb 026-06 (release 2026.5)
     * the transformation ran after the go point, and an exception or a result over L4 failed
     * the database.</p>
     * 
     * @param transTime The time of the transaction. Also functions as a unique transaction
     * ID.
     * @param inputValue The pre-execute() value of the KV.
     * @param previous The previous value for the key, or 'null' if no such value exists previously.
     * @return The value to set.
     */
    public byte[] transform(long transTime, byte[] inputValue, byte[] previous);
}
