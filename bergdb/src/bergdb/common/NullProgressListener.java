package bergdb.common;

/**
 * A ProgressListener that does nothing with the reported progress.
 * 
 * @author Frans Lundberg
 */
public class NullProgressListener implements ProgressListener {
    /**
     * This method does nothing.
     */
    public void progress(int progressValue, String note) {}
}
