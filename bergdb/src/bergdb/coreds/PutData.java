package bergdb.coreds;

import bergdb.coreds.Graph.CachePolicy;
import bergdb.coreds.Graph.NodeChangeListener;
import bergdb.coreds.Graph.PointerListener;

/**
 * Common for one put operation, or a set of put operations (a transaction).
 * 
 * @author Frans Lundberg
 */
public class PutData {
    static final KlongWithPointer[] zeroKwi = new KlongWithPointer[0];
    
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
    
    public NodeChangeListener nodeChangeListener;
    
    // ---- Listeners, cache policy and more ----
    
    public PointerListener pointerListener;
    
    public CachePolicy cachePolicy;
    
    public KeyAccessPath keyAccessPath;
    
    public Graph.SplitListener splitListener;
    
    /**
     * Creates a new PutData object directly.
     * Note: prefer to use Graph.newPutData() or Db.newPutData().
     */
    public PutData() {
        tt = 0;
        accessData = Spos.DEFAULT_ACCESS_DATA;
        spaceSplitCount = 0;
        
        tempPointer = new Pointer();
        kwi = new KlongWithPointer();
        oneKwi = new KlongWithPointer[1];
        oneKwi[0] = new KlongWithPointer();
        twoKwis = new KlongWithPointer[2];
        twoKwis[0] = new KlongWithPointer();
        twoKwis[1] = new KlongWithPointer();
        keyAccessPath = new KeyAccessPath();
        
        nodeChangeListener = Graph.DO_NOTHING_NODE_CHANGE_LISTENER;
        pointerListener = Graph.DO_NOTHING_POINTER_LISTENER;
        cachePolicy = Graph.CACHE_ALL_EXCEPT_LARGE_VALUE_NODES;
        splitListener = Graph.DO_NOTHING_SPLIT_LISTENER;
    }
    
    public void clearFast() {
        keyAccessPath.clearFast();
    }
    
    public void clear() {
        tempPointer.node = null;
        kwi.node = null;
        oneKwi[0].node = null;
        twoKwis[0].node = null;
        twoKwis[1].node = null;
        keyAccessPath.clear();
    }
    
    public KeyNode getParent(int depth) {
        assert (depth >= 0) : "depth = " + depth;
        
        int parentDepth = depth - 1;
        return parentDepth < 0 ? null : keyAccessPath.get(parentDepth);
    }
}