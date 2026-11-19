package bergdb.dag;

/**
 * Common data for one put operation, or a set of put operations (a transaction).
 * An instance can be reused between transactions for high performance reasons; just
 * call clear() and clearFast() between ops / between transactions.
 * 
 * @author Frans Lundberg
 */
public class PutData extends OpData {
    
    // ==== Input ====
    
    public Dag.NodeChangeListener nodeChangeListener;
    public Dag.PointerCreatedListener pointerCreatedListener;

    /** Test hook: run PE's plan even when the transaction qualifies for the short way. */
    boolean forcePePlan;
    
    // ==== Output ====
    
    /** Transaction time. */
    public long tt;
    
    /**
     * Creates a new PutData object directly.
     * Note: prefer using Graph.newPutData() instead of this constructor.
     */
    public PutData() {
        tt = 0;
        accessData = AccessData.DEFAULT_ACCESS_DATA;
        tempPointer = new Pointer();
        nodeChangeListener = Dag.DO_NOTHING_NODE_CHANGE_LISTENER;
        pointerListener = Dag.DO_NOTHING_POINTER_LISTENER;
        pointerCreatedListener = Dag.DO_NOTHING_POINTER_CREATED_LISTENER;
        cachePolicy = Dag.CACHE_ALL_EXCEPT_LARGE_VALUE_NODES;
    }
    
    /**
     * Called at the end of each Dag.putKvs() call. (Until record format 8, after each
     * operation of a transaction: it cleared the key access path of the old writer, gone with
     * it; bergdb 026-25.)
     */
    public void clearFast() {
        kwi.klong = Klong.NULL;
        kwi.node = null;
    }
    
    /**
     * Called at end of Db.putKvs() to clear for new transaction execution.
     */
    public void clear() {
        tempPointer.index = -1;
        tempPointer.node = null;
        tempPointer.pos = Spos.NULL;
        kwi.node = null;
        kwi.klong = Klong.NULL;
        kwi.klongTime = -1;
    }
}
