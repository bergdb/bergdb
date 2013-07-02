package bergdb.storage;

/**
 * An AppendListener that does nothing when notified.
 * 
 * @author Frans Lundberg
 */
public final class NullAppendListener implements AppendListener {
    /**
     * This method does nothing.
     */
    public final void dataAppended(long postStreamSize) {
        // empty
    }
}
