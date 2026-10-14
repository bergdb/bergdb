package bergdb.common;

/**
 * A ProgressListener that does nothing.
 * 
 * @author Frans Lundberg
 */
public class NullProgressListener implements ProgressListener {
    /**
     * This method does nothing.
     */
    public void progress(int progressValue, String note) {}
}
