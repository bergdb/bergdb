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
    
    // ==== The check of a descent for a cycle ====
    
    // Brent's cycle detection: the id of the node that the descent reached at its step 2^k,
    // the steps since then, and the steps until the next 2^k.
    private long descentMark;
    private int descentSteps;
    private int descentPower;
    
    /**
     * Starts the check of a descent from 'root' (descentTo()). A descent goes down a tree,
     * from a node to a node below it, so it never comes back to a node it passed, but on a
     * damaged stream it can (2026-11-10, CorruptStreamTester in the release night of 2026.4):
     * a key node's prevPos, changed with its checksum made right, named the version of its
     * own child before the startup section; the start's Rule R (DbStarter.createMaps(),
     * updateStreamPointers()) then made the pointer to that child, in the node's newest
     * version, a pointer to the node itself, and a get looped in
     * Dag.getEqNodeInSegment() without end.
     */
    public final void descentFrom(Node root) {
        descentMark = root.getId();
        descentSteps = 0;
        descentPower = 1;
    }
    
    /**
     * A step of the descent to 'next', the node that a pointer of the node before it names.
     * Throws pointerFollower's cycle() if the descent came back to a node it passed: Brent's
     * cycle detection keeps the id of the node of step 2^k and compares each node after it
     * with it, so a cycle is found within about twice the steps of the path and the cycle,
     * in constant memory and with no bound on a tree's height. The nodes of a valid tree's
     * path have distinct ids, so the check never fails a valid database; a node without an id
     * (Spos.NULL: a Dag without a Db, as in DagTester, or a version not yet given one) is
     * not compared. In a Db it is a StreamFormatException: a get that meets the cycle fails
     * the database (Db.readFailed()), as on other damage that a read finds, and a start that
     * meets it refuses the stream.
     */
    public final void descentTo(Node next) {
        final long id = next.getId();
        if (id == descentMark && id != Spos.NULL) {
            throw pointerFollower.cycle("A descent came back to key node " + id
                    + ", which it passed: the pointers make a cycle.");
        }
        if (++descentSteps == descentPower) {
            descentMark = id;
            descentPower <<= 1;
            descentSteps = 0;
        }
    }
}
