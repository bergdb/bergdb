package bergdb.dag;


/**
 * Data needed for an 'evict' operation.
 * An object of this class can be seen as an operation-local variable scope.
 * An object must not be used by multiple concurrent threads.
 * 
 * @author Frans Lundberg
 * @deprecated
 */
public class EvictData {
    public boolean enableEvict;     // Set by user.
    public Pointer tempPointer;     // Temporary data.
    public int evictCount;          // Set by Evictor. Number of evicted pointers
    public int totalCount;          // Set by Evictor. Total number of pointers processed
    public long startupPos;         // Set and used by Evictor.
    public long accessTimeLimit;    // Set and used by Evictor. 
                                    // A node with access time >= accessTimeLimit is not evictable.
    public int reasonAccessTime;
    public int reasonDirty;
    public int reasonNotMem;
    
    public EvictData() {
        tempPointer = new Pointer();
        enableEvict = true;
    }
}
