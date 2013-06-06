package kissdb.common;

/**
 * Reports progress, results, or whatever.
 * 
 * @author Frans Lundberg
 */
public interface ReportHandler {
    
    /**
     * Reports things by setting parameters.
     * Some names are standard.
     * String "message" is general human output, can be sent to human end user.
     * String "debug" is debug messages for programmers.
     * Double "progress" is a progress value between 0.0 (for just started) 
     * to 1.0 (done).
     */
    public void report(String name, Object value);
}
