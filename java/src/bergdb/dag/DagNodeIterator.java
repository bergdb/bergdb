package bergdb.dag;

import bergdb.common.Pair;

/**
 * Iterates all nodes in a DAG.
 * Nodes may be iterated several times, a depth-first tree search algorithm is used.
 * Note: the PointerFollower may need to be changed.
 * 
 * @author Frans Lundberg
 */
public class DagNodeIterator {
    // Depth-first DAG traversial.
    
    private Dag dag;
    private Node root;
    private boolean rootAdded = false;
    private int nextPointerIndex = 0;
    private DagNodeIterator iter;
    private long maxLookupTime;
    private GetData gd;
    /**
     * For the iterator whose next() is called: the chain of iterators from it to the one
     * at the walk's place, or null before the first call (bergdb 021-16).
     */
    private java.util.ArrayList<DagNodeIterator> path = null;
    
    public DagNodeIterator(Dag dag) {
        this.dag = dag;
        this.root = dag.getTopDs().getSuperRoot();
        this.maxLookupTime = Long.MAX_VALUE;
        initGd();
    }
    
    public DagNodeIterator(Dag dag, Node root, long maxLookupTime) {
        this.dag = dag;
        this.root = root;
        this.maxLookupTime = maxLookupTime;
        initGd();
    }
    
    private void initGd() {
        gd = dag.newGetData();
        gd.accessData = AccessData.ZERO;
        gd.pointerFollower = new PointerFollower() {
            public Node followPointer(Node predecessor, int pointerIndex, OpData op) {
                Node result;
                assert pointerIndex >= 0 : "pointerIndex: " + pointerIndex;
                assert predecessor != null : "predecessor is null";

                Node pointerNode = predecessor.getPointerNode(pointerIndex);
                long pointerPos1 = predecessor.getPointerPos(pointerIndex);

                assert !Pointer.isNull(pointerNode, pointerPos1) : "Pointer is null: " + pointerNode
                        + ", " + pointerPos1;

                if (Pointer.isMem(pointerNode)) {
                    result = pointerNode;
                    op.pointerListener.pointerFollowed(predecessor, pointerIndex, result, Pointer.TYPE_MEMORY);
                
                } else {
                    throw new IllegalStateException("This NodeFollower does not support stream pointers.");
                }

                return result;
            }
        };
    }
    
    /**
     * Returns node or null when done.
     * 
     * <p>An iterator's next node is its root, then the nodes of the iterator of its first
     * child, then of its next child, and so on. The iterators of the children form a chain,
     * one per level of the walk, and next() follows the chain in a loop, kept in 'path'
     * between the calls, not by a recursion down the chain at each call, as until bergdb
     * 021-16: a key has a level of key nodes per segment of 7 bytes, so a long key made the
     * recursion overflow the thread's stack, and each call took time in the depth.</p>
     */
    public Node next() {
        if (path == null) {
            path = new java.util.ArrayList<DagNodeIterator>();
            path.add(this);
        }
        while (!path.isEmpty()) {
            final DagNodeIterator it = path.get(path.size() - 1);
            if (!it.rootAdded) {
                it.createChildIter(it.maxLookupTime);
                it.rootAdded = true;
                return it.root;
            }
            if (it.iter != null) {
                path.add(it.iter);
                continue;
            }
            // 'it' is done: the iterator above it goes on with its next child.
            path.remove(path.size() - 1);
            if (!path.isEmpty()) {
                final DagNodeIterator above = path.get(path.size() - 1);
                above.createChildIter(above.maxLookupTime);
            }
        }
        return null;
    }
    
    private void createChildIter(long maxLookupTime) {
        Pair<Long, Node> result = getChild(nextPointerIndex, maxLookupTime);
        maxLookupTime = result.value0();
        Node child = result.value1();
        
        if (child == null) {
            iter = null;
        } else {
            iter = new DagNodeIterator(dag, child, maxLookupTime);
            nextPointerIndex++;
        }
    }
    
    /**
     * Gets new maxLookupTime and next child.
     */
    private Pair<Long, Node> getChild(int pointerIndex, long maxLookupTime) {
        int n = root.getSizeAtTime(maxLookupTime);
        
        Pointer p = new Pointer();
        
        while (pointerIndex < n) {
            root.getPointer(pointerIndex, p);
            if (!p.isNull()) {
                nextPointerIndex = pointerIndex;
                break;
            }
            
            pointerIndex++;
        }
        
        if (p.isNull()) {
            return new Pair<Long, Node>(maxLookupTime, null);
        }
        
        long newMaxLookupTime = maxLookupTime;
        if (root.isKeyNode()) {
            KeyNode keyNode = (KeyNode) root;
            
            long klong = keyNode.klongs[pointerIndex];
            if (Klong.getType(klong) != Klong.TYPE_KEY) {
                throw new Error("pointer not null but klong type is not TYPE_KEY, klong: " 
                        + Klong.toString(klong) + ", p: " + p.toString());
            }
            
            long maxValidTime = keyNode.getMaxValidTime(pointerIndex);
            if (maxValidTime < maxLookupTime) {
                newMaxLookupTime = maxValidTime;
            }
        }
        
        Node child = gd.followPointer(root, pointerIndex);
        
        return new Pair<Long, Node>(newMaxLookupTime, child);
    }
    
    // ======== Test ========
}
