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
     * <p>The implementation of this method must not throw any exception, as for
     * KeyTransformation. It runs after the transaction's go point, in Db.putKvs(), where
     * nothing refuses a transaction; an exception there fails the database (bergdb 005-01).
     * The previous value is the one before the transaction.</p>
     * 
     * <p>Its result is not size-checked (bergdb 015-51). The check of the transaction's size
     * before the go point (Db.checkSize, bergdb 005-17) counts inputValue: the result must
     * keep the transaction's value nodes, with its other values, within
     * StoredTrans.valueLimit(), 7/8 of the record limit (about 1.88 GB), as a value given
     * directly must. A larger result is the caller's fault, as an exception is: one whose
     * record does not fit the record limit fails the database when the record is made,
     * and the transaction is not in the stream.</p>
     * 
     * @param transTime The time of the transaction. Also functions as a unique transaction
     * ID.
     * @param inputValue The pre-execute() value of the KV.
     * @param previous The previous value for the key, or 'null' if no such value exists previously.
     * @return The value to set.
     */
    public byte[] transform(long transTime, byte[] inputValue, byte[] previous);
}
