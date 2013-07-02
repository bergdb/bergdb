package bergdb.common;

/**
 * This ReportHandler that does nothing.
 * 
 * @author Frans Lundberg
 */
public class NullReportHandler implements ReportHandler {
    /** Does nothing. */
    public void report(String name, Object value) {
    }
}
