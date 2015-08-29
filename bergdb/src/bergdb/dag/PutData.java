package bergdb.dag;

/**
 * Common for one put operation, or a set of put operations (a transaction).
 * Is reused between transactions for performance reasons.
 * 
 * @author Frans Lundberg
 */
public class PutData {
    
    /** Transaction time. */
    public long tt;
    
    /** Access data. */
    public long accessData;
    
    /** Counter of space splits. */
    public long spaceSplitCount;
    
    /** Counter of time splits. */
    public long timeSplitCount;
    
    
    // ---- Temp data ---
    
    /** Temporary working data. */
    public final Pointer tempPointer;
    
    /** Temporary working data. */
    public final KlongWithPointer kwi;
    
    /** Temporary working data, length == 1. */
    public final KlongWithPointer[] oneKwi;
    
    /** Temporary working data, length == 2. */
    public final KlongWithPointer[] twoKwis;
    
    
    // ---- Listeners, cache policy ----
    
    public Dag.NodeChangeListener nodeChangeListener;
    
    public Dag.PointerListener pointerListener;
    
    public Dag.PointerCreatedListener pointerCreatedListener;
    
    public Dag.CachePolicy cachePolicy;
    
    public KeyAccessPath keyAccessPath;
    
    public Dag.SplitListener splitListener;
    
    
    
    /**
     * Creates a new PutData object directly.
     * Note: prefer using Graph.newPutData() instead of this constructor.
     */
    public PutData() {
        tt = 0;
        accessData = AccessData.DEFAULT_ACCESS_DATA;
        spaceSplitCount = 0;
        
        tempPointer = new Pointer();
        kwi = new KlongWithPointer();
        oneKwi = new KlongWithPointer[1];
        oneKwi[0] = new KlongWithPointer();
        twoKwis = new KlongWithPointer[2];
        twoKwis[0] = new KlongWithPointer();
        twoKwis[1] = new KlongWithPointer();
        keyAccessPath = new KeyAccessPath();
        
        nodeChangeListener = Dag.DO_NOTHING_NODE_CHANGE_LISTENER;
        pointerListener = Dag.DO_NOTHING_POINTER_LISTENER;
        pointerCreatedListener = Dag.DO_NOTHING_POINTER_CREATED_LISTENER;
        cachePolicy = Dag.CACHE_ALL_EXCEPT_LARGE_VALUE_NODES;
        splitListener = Dag.DO_NOTHING_SPLIT_LISTENER;
    }
    
    /**
     * Called at end of each putKv() call.
     */
    public void clearFast() {
        keyAccessPath.clearFast();
        kwi.klong = Klong.NULL;
        kwi.node = null;
    }
    
    /**
     * Called at end of Db.putKvs() to clear for new transaction execution.
     */
    public void clear() {
        keyAccessPath.clear();
        tempPointer.index = -1;
        tempPointer.node = null;
        tempPointer.pos = Spos.NULL;
        
        kwi.node = null;
        kwi.klong = Klong.NULL;
        kwi.klongTime = -1;
        
        oneKwi[0].node = null;
        twoKwis[0].node = null;
        twoKwis[1].node = null;
    }
    
    public KeyNode getParent(int depth) {
        assert (depth >= 0) : "depth = " + depth;
        
        int parentDepth = depth - 1;
        return parentDepth < 0 ? null : keyAccessPath.get(parentDepth);
    }
}