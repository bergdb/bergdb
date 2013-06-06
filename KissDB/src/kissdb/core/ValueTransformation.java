package kissdb.core;

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
     * @param transactionTime The time of the transaction. Also functions as a unique transaction
     * ID.
     * @param inputValue The pre-execute() value of the KV.
     * @param previous The previous value for the key, or 'null' if no such value exists previously.
     * @return The value to set.
     */
    public byte[] transform(long transactionTime, byte[] inputValue, byte[] previous);
}
