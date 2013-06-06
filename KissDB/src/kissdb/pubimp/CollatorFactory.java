package kissdb.pubimp;

public interface CollatorFactory {
    /**
     * Creates a new collator based in the given typeString.
     * 
     * @return The collator object or null if no collator can be created for the given typeString.
     */
    public KCollator createCollator(String typeString);
    
    /**
     * Returns true if the index type is supported.
     */
    public boolean typeSupported(String typeString);
}
