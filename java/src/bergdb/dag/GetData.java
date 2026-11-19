package bergdb.dag;

/**
 * Data needed for a database get operation (Db.getOne(), getMany()).
 * An object of this class can be seen as an operation-local variable scope.
 * A GetData object can be reused between serial get requests, but the same GetData 
 * object must not be used by multiple threads for concurrent get operations.
 * 
 * <p>Its outputs after Db.getOne() (bergdb 020-24-09, U9-8): actualLookupTime, the time of
 * the state read, the requested lookup time or the last transaction's time if that is
 * earlier (Db, "Threads"); tpos, for a value found, the position of the transaction that
 * wrote it, which Db.getTrans() reads, reclaim's step for a value that reclaim has copied
 * forward (Db.getTrans()).</p>
 * 
 * @author Frans Lundberg
 */
public class GetData extends OpData {

    // ==== Input ====
    

    // ==== Output ====
    
    public long actualLookupTime;
        // The actual lookup time used. Can be less than the requested lookup time.
    /**
     * The time of the key node entry that points to the value found: not the time of the
     * write, but the time of the transaction that made the entry, the write's or a later one
     * (bergdb 021-19). PE makes every entry of a new key node anew, at its own time, in a
     * replacement, cut, join or compaction (bergdb 027-08), also those
     * of keys that it does not write; and reclaim, which copies a value forward, writes it
     * anew (see tpos). So the time is at or after the time of the write and at or before the
     * lookup time, and two reads of a value that did not change, at lookup times before and
     * after such a transaction, may give two times. For the time of the write, read the
     * transaction: Db.getTrans(tpos).tt (for a value that reclaim has copied, the step's; see
     * tpos). Not in the Pub API since 2026-10-13, and no reader of BergDB's own uses it
     * (bergdb 011-01, Q9: there is no exact value time; 011-04, W3).
     */
    public long kvTime;
    
    /**
     * The stream position of the transaction that stored the value found, for Db.getTrans():
     * the transaction that wrote it, or, for a value that reclaim has copied forward, reclaim's
     * step, whose time is the step's (bergdb 021-19). A get of the key at the step's time
     * less one gives the same value and the position of the transaction that stored it
     * before, the write's or an earlier step's, as the Pub API's Connection.transactionInfo()
     * follows it back (bergdb 021-17). Spos.NULL while the value's transaction is being
     * stored (Db.getTrans).
     */
    public long tpos;
    public long followMemoryPointerCount;
    public long followStreamPointerCount;
    
    
    // ==== Internal ====
    
    /** Depth in space Dag (TopNodes not counted). */
    public int nodeDepth;

    /**
     * Creates a new instance; prefer to use Graph.newGetData() or Db.newGetData().
     */
    public GetData() {
        tempPointer = new Pointer();
        pointerListener = Dag.DO_NOTHING_POINTER_LISTENER;        
        cachePolicy = Dag.CACHE_ALL_EXCEPT_LARGE_VALUE_NODES;
    }
}