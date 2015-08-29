package bergdb.dag;

import bergdb.dag.Dag.CachePolicy;
import bergdb.dag.Dag.PointerListener;

/**
 * The top data structure is used to find the space root node given
 * the the lookup time for the operation.
 * 
 * @author Frans Lundberg
 */
public class TopDs {
    private volatile TopNode superRoot;
    
    public interface DagForMe {
        public Node followPointer(final Node predecessor, int pointerIndex, 
                long accessData, PointerListener walker, CachePolicy cachPolicy);
    }
    
    public TopDs(TopNode superRoot) {
        if (superRoot == null) {
            throw new IllegalArgumentException("superRoot == null not allowed");
        }
        this.superRoot = superRoot;
    }
    
    /**
     * Creates a TopDS from the transaction time and the very first 
     * space root node.
     */
    public static TopDs createFromFirstRoot(long firstTime, KeyNode firstRoot, long accessData,
            Dag.PointerCreatedListener pointerCreationListener) {
        TopNode first = createSuperRootFromFirstKeyNode(firstTime, firstRoot, accessData, pointerCreationListener);
        return new TopDs(first);
    }
    
    public static TopNode createSuperRootFromFirstKeyNode(long firstTime, KeyNode firstRoot, 
            long accessData, Dag.PointerCreatedListener pointerCreationListener) {
        TopNode first = new TopNode(0, firstRoot, accessData, firstTime, Spos.NULL);
        pointerCreationListener.pointerCreated(first, 0, firstRoot);
        return first;
    }
    
    /**
     * Creates a new super root node.
     * Caller must hold DB.writeLock.
     * 
     * @param time  The transaction time.
     */
    public void newSuperRoot(long time, KeyNode newRoot, long accessData, 
            Dag.PointerCreatedListener pointerCreationListener) {
        
        TopNode newSuperRoot = new TopNode(superRoot.topNodeId + 1, newRoot, accessData, time, 
                Spos.NULL);
        final int h = newSuperRoot.pointersLength;
        final int id = newSuperRoot.topNodeId;
        
        pointerCreationListener.pointerCreated(newSuperRoot, 0, newRoot);
        
        for (int i = 0; i < h; i++) {
            if ((id & TopNode.power2(i)) != 0) {
                assert superRoot != null;
                assert superRoot.pointers != null;
                
                TopNode pointer = null;
                
                if (i < superRoot.pointersLength) {
                    pointer = superRoot.pointers[i];
                }
                
                if (pointer == null) {
                    pointer = superRoot;
                }
                
                newSuperRoot.pointers[i] = pointer;
                if (pointer == null) {
                    newSuperRoot.pointersTime[i] = -1;
                    newSuperRoot.pointersPos[i] = Spos.NULL;
                } else {
                    newSuperRoot.pointersTime[i] = pointer.rootTime;
                    newSuperRoot.pointersPos[i] = accessData;
                    
                    pointerCreationListener.pointerCreated(newSuperRoot, i + 1, pointer);
                }
            }
        }
        
        this.superRoot = newSuperRoot;    // volatile write, publishes changes to readers
    }
    
    public final TopNode getSuperRoot() {
        // volatile read, synchs previous writes.
        return superRoot;
    }
    
    /**
     * Convenience method for when GetData is used.
     */
    public final KeyNode findRoot(DagForMe dbGraph, long time, GetData gd) {
        return findRoot(dbGraph, time, gd.accessData, gd.tempPointer, gd.pointerListener, gd.cachePolicy);
    }
    
    /**
     * Finds the space root node for a given lookup time.
     * Returns null if there is no space root that is old enough.
     * 
     * @param accessData Access data for this access.
     */
    public final KeyNode findRoot(DagForMe dag, long time, long accessData, 
            Pointer tempPointer, PointerListener pointerListener, CachePolicy cachePolicy) {
        TopNode n = findSuperRootAtTime(dag, time, accessData, tempPointer, pointerListener, cachePolicy);
        if (n == null) {
            return null;
        }
        return (KeyNode) dag.followPointer(n, 0, accessData, pointerListener, cachePolicy);
    }
    
    /**
     * Convenience method for when GetData is used.
     */
    public final TopNode findSuperRootAtTime(DagForMe dbGraph, long time, GetData gd) {
        return findSuperRootAtTime(dbGraph, time, gd.accessData, gd.tempPointer, 
                gd.pointerListener, gd.cachePolicy);
    }
    
    /**
     * Finds the top node that was super root node at a given time.
     * Returns null if there is no accessible top node that was 
     * super root at the given time.
     * 
     * @param accessData Access data for this access.
     */
    public final TopNode findSuperRootAtTime(DagForMe dag, long time, long accessData, 
            Pointer tempPointer, PointerListener pointerListener, CachePolicy cachePolicy) {
        //
        // 130123 Frans: Fixed concurrency bug.
        // The volatile read in the beginning of this method is important. It makes memory writes
        // by writer visible and it makes sure we are using the same superRoot instance
        // throughout this method. this.superRoot can change concurrently.
        //
        
        assert pointerListener != null;
        assert cachePolicy != null;
        
        TopNode mySuperRoot = this.superRoot;     // volatile read make writes visible.
        
        pointerListener.superRootAccessed(mySuperRoot);
        
        if (time >= mySuperRoot.rootTime) {
            return mySuperRoot;
        }
        
        TopNode n = mySuperRoot;
        
        // Finds right-most pointer with time >= 'time'.
        
        Pointer pt = tempPointer;
        
        while (true) {
            rightMostGte(n, time, pt);
            if (pt.isNull()) {
                break;
            }
            
            n = (TopNode) dag.followPointer(n, pt.index, accessData, pointerListener, cachePolicy);
        }
        
        
        if (n.rootTime == time) {
            return n;
        }
        
        // Find left-most pointer
        
        pt.reset();
        leftMost(n, time, pt);
        
        if (pt.isNull()) {
            return null;  // No old-enough node exists
        }
        
        TopNode n2 = (TopNode) dag.followPointer(n, pt.index, accessData, pointerListener, cachePolicy);
        assert n2 != null : "n2 is unexpectedly null, n: " + n;
        
        return n2;
    }
    
    /**
     * 
     * @param p  Output param, contains the result after method invocation.
     */
    private void rightMostGte(TopNode n, long t, Pointer p) {
        p.reset();
        
        for (int i = n.pointersLength - 1; i >= 0; i--) {
            TopNode top = n.pointers[i];
            if (Pointer.isNull(top, n.pointersPos[i])) {
                continue;
            }
            
            if (n.pointersTime[i] >= t) {
                p.node = top;
                p.pos = n.pointersPos[i];
                p.index = i + 1;      // +1 because root pointer has index 0.
                break;
            }
        }
    }
    
    private void leftMost(TopNode n, long t, Pointer p) {
        p.reset();
        final int pointersLength = n.pointersLength;
        
        for (int i = 0; i < pointersLength; i++) {
            TopNode top = n.pointers[i];
            
            if (Pointer.isNull(top, n.pointersPos[i])) {
                continue;
            }
            
            if (t >= n.pointersTime[i]) {
                p.node = top;
                p.pos = n.pointersPos[i];
                p.index = i + 1;  // +1 since root pointer has index 0.
            }
            
            break;
        }
    }
    
    /**
     * Prints the top data structure to a multi-line string.
     */
    public String print(DagForMe dbGraph) {
        StringBuilder b = new StringBuilder();
        TopNode t = this.superRoot;
        long accessData = 0;
        Dag.PointerListener pListener = Dag.DO_NOTHING_POINTER_LISTENER;
        Dag.CachePolicy cachePolicy = Dag.CACHE_NOTHING;
        
        while (t != null) {
            b.append(String.format("%6d", t.topNodeId));
            b.append(String.format(" (%2d) ", t.rootTime));
            for (int i = 0; i < t.pointersLength; i++) {
                if (t.pointers[i] == null) {
                    b.append(String.format("%3s", " x "));
                } else {
                    b.append(String.format("%3s", " | "));
                }
            }
            b.append("\n");
            
            TopNode next = null;
            for (int i = 0; i < t.pointersLength; i++) {
                if (t.pointers[i] != null && next == null) {
                    next = (TopNode) dbGraph.followPointer(t, i, 
                            accessData, pListener, cachePolicy);
                    break;
                }
            }
            
            t = next;
        }
        
        return b.toString();
    }
}

/*

======== Notes, 2012-05, Frans Lundberg ========

See doc/2012-05-TopDB.txt.

*/