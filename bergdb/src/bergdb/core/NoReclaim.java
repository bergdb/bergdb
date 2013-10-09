package bergdb.core;

import bergdb.stream.AppendOnlyStream;


/**
 * A subclass of Reclaim that does not do any reclaim.
 * Useful for testing only.
 * 
 * @author Frans Lundberg
 */
public class NoReclaim extends Reclaim {
    public NoReclaim(Db db, AppendOnlyStream aos) {
        super(db, aos);
        System.out.println("core.NoReclaim created");
    }

    public final void transactionCompleted(Trans t) {
        // empty
    }
}
