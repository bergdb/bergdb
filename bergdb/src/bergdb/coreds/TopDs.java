package bergdb.coreds;

import bergdb.coreds.Graph.CachePolicy;
import bergdb.coreds.Graph.PointerListener;

/**
 * The top data structure is used to find the space root node given
 * the the lookup time for the operation.
 * 
 * @author Frans Lundberg
 */
public class TopDs {
    private volatile TopNode superRoot;
    
    public interface DbGraphForMe {
        public INode followPointer(final INode predecessor, int pointerIndex, 
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
    public static TopDs createFromFirstRoot(long firstTime, KeyNode firstRoot, long accessData) {
        TopNode first = new TopNode(0, firstRoot, accessData, firstTime, Spos.NULL);
        TopDs ds = new TopDs(first);
        return ds;
    }
    
    /**
     * Creates a new super root node.
     * Caller must hold DB.writeLock.
     * 
     * @param time  The transaction time.
     */
    public void newSuperRoot(long time, KeyNode newRoot, long accessData) {
        TopNode newSuperRoot = new TopNode(superRoot.topNodeId + 1, newRoot, accessData, time, 
                Spos.NULL);
        final int h = newSuperRoot.pointersLength;
        final int id = newSuperRoot.topNodeId;
        
        for (int i = 0; i < h; i++) {
            if ((id & TopNode.power2[i]) != 0) {
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
     * 
     * @see #findRoot(DbGraphForMe, long, long, Pointer, PointerListener, CachePolicy)
     */
    public final KeyNode findRoot(DbGraphForMe dbGraph, long time, GetData gd) {
        return findRoot(dbGraph, time, gd.accessData, gd.tempPointer, gd.pointerListener, gd.cachePolicy);
    }
    
    /**
     * Finds the space root node for a given lookup time.
     * Returns null if there is no space root that is old enough.
     * 
     * @param accessPath Adds top nodes to the access path if non-null.
     * The returned node is not added to this access path (it cannot be done, since it is not a
     * TopNode).
     * @param accessData Access data for this access.
     */
    public final KeyNode findRoot(DbGraphForMe dbGraph, long time, long accessData, 
            Pointer tempPointer, PointerListener pointerListener, CachePolicy cachePolicy) {
        //
        // The common case of getting the last space root is treated as a 
        // special case for performance.
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
            return (KeyNode) dbGraph.followPointer(mySuperRoot, 0, accessData, pointerListener, cachePolicy);
        }
        
        TopNode n = mySuperRoot;
        
        // Finds right-most pointer with time >= 'time'.
        
        Pointer pt = tempPointer;
        
        while (true) {
            rightMostGte(n, time, pt);
            if (pt.isNull()) {
                break;
            }
            
            n = (TopNode) dbGraph.followPointer(n, pt.index, accessData, pointerListener, cachePolicy);
        }
        
        
        if (n.rootTime == time) {
            return (KeyNode) dbGraph.followPointer(n, 0, accessData, pointerListener, cachePolicy);
        }
        
        // Find left-most pointer
        
        pt.reset();
        leftMost(n, time, pt);
        
        if (pt.isNull()) {
            return null;  // No old-enough node exists
        }
        
        TopNode n2 = (TopNode) dbGraph.followPointer(n, pt.index, accessData, pointerListener, cachePolicy);
        assert n2 != null : "n2 is unexpectedly null, n: " + n;
        
        return (KeyNode) dbGraph.followPointer(n2, 0, accessData, pointerListener, cachePolicy);
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
    public String print(DbGraphForMe dbGraph) {
        StringBuilder b = new StringBuilder();
        TopNode t = this.superRoot;
        long accessData = 0;
        Graph.PointerListener pListener = Graph.DO_NOTHING_POINTER_LISTENER;
        Graph.CachePolicy cachePolicy = Graph.CACHE_NOTHING;
        
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