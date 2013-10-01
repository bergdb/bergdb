package bergdb.coreds;

import bergdb.coreds.Graph.CachePolicy;
import bergdb.coreds.Graph.NodeChangeListener;
import bergdb.coreds.Graph.PointerListener;

/**
 * Common for one put operation, or a set of put operations (a transaction).
 */
public class PutData {
    static final KlongWithPointer[] zeroKwi = new KlongWithPointer[0];
    
    /** Transaction time. */
    public long tt;
    
    /** Access data. */
    public long accessData;
    
    /**
     * Counter of number of splits.
     */
    public long splitCount;
    
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
    
    /**
     * Creates a new PutData object with default values.
     */
    public PutData() {
        tt = 0;
        accessData = -100;
        splitCount = 0;
        
        tempPointer = new Pointer();
        kwi = new KlongWithPointer();
        oneKwi = new KlongWithPointer[1];
        oneKwi[0] = new KlongWithPointer();
        twoKwis = new KlongWithPointer[2];
        twoKwis[0] = new KlongWithPointer();
        twoKwis[1] = new KlongWithPointer();
        keyAccessPath = new KeyAccessPath();
        
        nodeChangeListener = Graph.DO_NOTHING_NODE_CHANGE_LISTENER;
        
        pointerListener = new Graph.PointerListener() {
            public void pointerFollowed(INode predecessor, int pointerIndex, INode result, int pointerType) { 
                if (result != null) {
                    if (result.getType() == INode.TYPE_KEY_NODE) {
                        if (predecessor.getType() == INode.TYPE_TOP_NODE) {
                            keyAccessPath.add(Klong.NULL, (KeyNode) result); 
                        } else if (predecessor.getType() == INode.TYPE_KEY_NODE) {
                            KeyNode pre = (KeyNode) predecessor;
                            KeyNode res = (KeyNode) result;
                            keyAccessPath.add(pre.getKlong(pointerIndex), res);
                        }
                    }
                }
            }

            public void superRootAccessed(TopNode superRoot) {}
        };
        
        cachePolicy = Graph.CACHE_ALL_EXCEPT_LARGE_VALUE_NODES;
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
        int parentDepth = depth - 1;
        return parentDepth < 0 ? null : keyAccessPath.get(parentDepth);
    }
}