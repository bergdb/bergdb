package bergdb.dag;

/**
 * Data needed by a database operation (put, getOne, getMany).
 * An instance of this class functions as an operation-local variable
 * scope. It is useful to save memory and for fast data processing
 * while avoiding Db-global data.
 * 
 * @author Frans Lundberg
 */
public abstract class OpData {
    
    // ==== Input ====
    // Input, settings for this operation.
    
    public PointerFollower pointerFollower;
    
    public Dag.PointerListener pointerListener;  
    
    public Dag.CachePolicy cachePolicy;
    
    public long accessData; 
        // See dag.AccessData; use the functions in that class to 
        // interpret and update this value.
    
    
    // ==== Internal ====
    
    /** A pointer object for temporary working data. */
    public Pointer tempPointer;
    
    /** A KlongWithPointer for temporary working data. */
    public final KlongWithPointer kwi;
    
    public OpData() {
        kwi = new KlongWithPointer();
    }
    
    public Node followPointer(Node predecessor, int pointerIndex) {
        assert pointerFollower != null : "OpData.pointerFollower is null, not allowed";
        return pointerFollower.followPointer(predecessor, pointerIndex, this);
    }
}
