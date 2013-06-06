package kissdb.common;

/**
 * This interface is used for something that listens to progress.
 * 
 * @author Frans Lundberg
 */
public interface ProgressListener {
    
    /**
     * Called to report progress.
     * 
     * @param progressValue Set to between (no progress) to 100 (done) or to -1 (unknown progress). 
     * @param note  One-line sentence with human-readable information about the current progress.
     */
    public void progress(int progressValue, String note);
}
