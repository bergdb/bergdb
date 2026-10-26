package bergdb.dag;

/**
 * Data needed for a database get operation (Db.getOne(), getMany()).
 * An object of this class can be seen as an operation-local variable scope.
 * A GetData object can be reused between serial get requests, but the same GetData 
 * object must not be used by multiple threads for concurrent get operations.
 * 
 * @author Frans Lundberg
 */
public class GetData extends OpData {

    // ==== Input ====
    

    // ==== Output ====
    
    public long actualLookupTime;
        // The actual lookup time used. Can be less than the requested lookup time.
    public long kvTime;
        // The time of the key node entry of the found kv. Internal. NOT the time the kv was
        // written: after a time split of the key node it is the time of the split, and reclaim
        // rewrites values in later transactions. Not in the Pub API since 2026-10-13
        // (bergdb 011-01, Q9; bergdb 011-04, W3).
    public long tpos;
        // Set to the tpos of the transaction that wrote the value.
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