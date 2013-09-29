package bergdb.coreds;

/**
 * Data needed for a 'get' operation.
 * An object of this class can be seen as an operation-local variable scope.
 * A GetData object can be reused between serial get requests, but the same GetData 
 * object must not be used for concurrent get requests.
 * 
 * @author Frans Lundberg
 */
public class GetData {
    
    // -- Input, settings --
    
    public Graph.PointerListener pointerListener;
    
    public Graph.CachePolicy cachePolicy;
    
    
    // -- Internal working data --
    
    public final KlongWithPointer kwi;
        // Temporary working data.
    public final Pointer tempPointer;
        // Temporary working data.
    public int nodeDepth;
        // Depth in space node tree (TopNodes not counted). Output and working data.
    public long accessData; 
        // "Time" of the get operation measured in an internal time scale.
    public final EvictData evictData;
        // Internal data for DB.evict().
    
    // -- Output --
    
    public long actualLookupTime;
        // The actual lookup time used. Can be less than the requested lookup time.
    public long kvTime;
        // Set to the time the found kv was written to the database.
    public long followMemoryPointerCount;
    public long followStreamPointerCount;
    
    public GetData() {
        kwi = new KlongWithPointer();
        tempPointer = new Pointer();
        evictData = new EvictData();
        
        pointerListener = new Graph.PointerListener() {
            public void pointerFollowed(INode predecessor, int pointerIndex, INode result, int pointerType) {
                switch (pointerType) {
                case Pointer.TYPE_MEMORY:
                    GetData.this.followMemoryPointerCount++;
                    break;
                case Pointer.TYPE_STREAM:
                    GetData.this.followStreamPointerCount++;
                    break;
                default:
                    assert false : "Bad pointer type: " + pointerType + ".";
                }
            }
        };
        
        cachePolicy = Graph.CACHE_ALL_EXCEPT_LARGE_VALUE_NODES;
    }
}