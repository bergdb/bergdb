package bergdb.graph;


/**
 * Data needed for an 'evict' operation.
 * An object of this class can be seen as an operation-local variable scope.
 * An object must not be used by multiple concurrent threads.
 * 
 * @author Frans Lundberg
 */
public class EvictData {
    public boolean enableEvict;
    public Pointer tempPointer;     // temporary data
    public int evictCount;          // number of evicted pointers
    public int pointerCount;        // number of pointers processed
    public long startupPos;         // Index nodes with spos >= dirtyLimit must not be evicted
    
    public EvictData() {
        tempPointer = new Pointer();
        enableEvict = true;
    }
}
