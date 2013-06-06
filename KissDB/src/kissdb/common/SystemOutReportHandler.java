package kissdb.common;

/**
 * Reports progress to System.out.
 * 
 * @author Frans Lundberg
 */
public class SystemOutReportHandler implements ReportHandler {
    public void report(String name, Object value) {
        System.out.println("Reporter, " + name + " = " + value);
    }
}
