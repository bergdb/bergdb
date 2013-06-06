package kissdb.pubimp;

/**
 * Simple interface for a string comparison "collator" than creates a sort key ("sort bytes")
 * given a String. 
 * 
 * @author Frans Lundberg
 */
public interface KCollator {
    /**
     * Returns the "sort bytes", the collator key byte in a byte array. For all collators 
     * except for PrimaryKeyCollator, the last byte must be 0.
     */
    public byte[] getSortBytes(String s);
}
