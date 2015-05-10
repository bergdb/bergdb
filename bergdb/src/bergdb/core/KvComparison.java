package bergdb.core;

import java.io.PrintStream;

import bergdb.stream.AppendOnlyStream;
import bergdb.stream.ReadOnlyStream;

/**
 * Compares to databases for equality.
 * Call constructor, settings (out), then compare().
 * Do not call compare() more than once.
 * 
 * @author Frans Lundberg
 */
public class KvComparison {
    private final Db db1;
    private final Db db2;
    private PrintStream out = System.out;
    
    public KvComparison(Db db1, Db db2) {
        this.db1 = db1;
        this.db2 = db2;
    }
    
    public static KvComparison comparisonWithRestarted(Db db1) {
        AppendOnlyStream stream = db1.internal().getMainStream();
        ReadOnlyStream ro = new ReadOnlyStream(stream, false);
        Db db2 = Db.builder().mainStream(ro).start();
        return new KvComparison(db1, db2);
    }
    
    public KvComparison out(PrintStream out) {
        this.out = out;
        return this;
    }
    
    public boolean compare() {
        DbScan.Result r1 = new DbScan(db1).includeKvTime(true).scan();
        DbScan.Result r2 = new DbScan(db2).includeKvTime(true).scan();
        
        if (r1.kvCount != r2.kvCount) {
            String message = "Restarted Db has different kv count, orig: " 
                    + r1.kvCount + ", restarted (diff): " + (r2.kvCount - r1.kvCount);
            out.println(message);
            return false;
        } else if (r1.checksum != r2.checksum) {
            String message = "Restarted Db has same kv count but different checksums.";
            out.println(message);
            return false;
        }
        
        return true;
    }
}
