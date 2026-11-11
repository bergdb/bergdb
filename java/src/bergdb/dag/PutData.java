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
    public KeyAccessPath keyAccessPath;
    public Dag.SplitListener splitListener;
    
    
    // ==== Output ====
    
    /** Transaction time. */
    public long tt;
    
    /** Counter of space splits. */
    public long spaceSplitCount;
    
    /** Counter of time splits. */
    public long timeSplitCount;
    
    
    // ==== Internal ====

    
    /** Temporary working data, length == 1. */
    public final KlongWithPointer[] oneKwi;
    
    /** Temporary working data, length == 2. */
    public final KlongWithPointer[] twoKwis;
    
    
    /**
     * Creates a new PutData object directly.
     * Note: prefer using Graph.newPutData() instead of this constructor.
     */
    public PutData() {
        tt = 0;
        accessData = AccessData.DEFAULT_ACCESS_DATA;
        spaceSplitCount = 0;
        
        tempPointer = new Pointer();
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
        replaced.clear();
        replacedTime = -1;
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
    
    /**
     * The nodes that the splits of the transaction at time 'replacedTime' made, each with the
     * node that existed before it and that it replaces (bergdb 023-05, P1): a split's last
     * version, halves and new root. A node made by the transaction and emptied in it is taken
     * back through it (Dag.takeBack).
     */
    private final java.util.IdentityHashMap<KeyNode, KeyNode> replaced =
            new java.util.IdentityHashMap<KeyNode, KeyNode>();
    private long replacedTime = -1;
    
    /** Records that 'made', made by the split at tt, replaces 'old', null: no such node. */
    void madeFor(KeyNode made, KeyNode old) {
        if (replacedTime != tt) {
            replaced.clear();
            replacedTime = tt;
        }
        if (old != null) {
            replaced.put(made, old);
        }
    }
    
    /** The node that 'made', made by a split of this transaction, replaces; else null. */
    KeyNode replacedBy(KeyNode made) {
        return replacedTime == tt ? replaced.get(made) : null;
    }
    
    public KeyNode getParent(int depth) {
        assert (depth >= 0) : "depth = " + depth;
        
        int parentDepth = depth - 1;
        return parentDepth < 0 ? null : keyAccessPath.get(parentDepth);
    }
}