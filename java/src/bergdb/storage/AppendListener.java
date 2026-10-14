package bergdb.storage;


/**
 * An AppendOnlyStream can have a listener that is notified after data has been appended to the
 * AppendOnlyStream.
 * 
 * @see BufferedStream
 * @author Frans Lundberg
 */
public interface AppendListener {
    
    /**
     * Tells listener implementation that data has been appended to the stream.
     * 
     * @param postStreamLength  The new stream length after the append operation.
     */
    public void dataAppended(long postStreamLength);
    
    /**
     * Tells listener implementation that an append to the stream failed. The bytes were
     * not appended, and the stream accepts no more appends.
     */
    public void appendFailed(java.io.IOException e);
}
