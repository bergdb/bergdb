package bergdb.dag;

/**
 * The top data structure is used to find the space root node given
 * the the lookup time for the operation.
 * 
 * @author Frans Lundberg
 */
public class TopDs {
    private volatile TopNode superRoot;
    
    /**
     * The ordinal of the top node after the first: 1, or for tests a larger one
     * (setSecondOrdinal). Synch note: set at startup, before the first transaction.
     */
    private long secondOrdinal = 1;
    
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
     * For tests (DbBuilder.secondTopOrdinal; bergdb item 005-02): the top node after the
     * first gets this ordinal instead of 1, so that a test reaches large ordinals without
     * making as many top nodes. Its skip pointers name the first top node, as newSuperRoot
     * does for a skip pointer that the super root lacks.
     */
    public void setSecondOrdinal(long ordinal) {
        if (ordinal < 1 || ordinal > TopNode.MAX_TOP_NODE_ID_VALUE) {
            throw new IllegalArgumentException("Bad ordinal, " + ordinal + ".");
        }
        this.secondOrdinal = ordinal;
    }
    
    /**
     * Creates a new super root node.
     * Caller must hold Db.writeLock.
     * 
     * @param time  The transaction time.
     */
    public void newSuperRoot(long time, KeyNode newRoot, long accessData, 
            Dag.PointerCreatedListener pointerCreationListener, Dag.NodeChangeListener nodeChangeListener) {

        if (time == superRoot.rootTime) {
            // A second new space root in the same transaction, for example a time split
            // of the root followed by a space split. Top node times must be strictly
            // increasing; findSuperRootAtTime() can return the wrong one of two top nodes
            // with the same time. The super root was created by this transaction, so it
            // is not yet written and no reader uses its root pointer (readers have
            // lookup time < time). Update it instead of creating a new top node.
            superRoot.setPointer(0, newRoot, accessData);
            pointerCreationListener.pointerCreated(superRoot, 0, newRoot);
            return;
        }

        assert time > superRoot.rootTime : "time " + time + " < " + superRoot.rootTime;

        // The ordinal: one more than the super root's (a long below 2^48 since bergdb item
        // 005-02; TopNode.MAX_TOP_NODE_ID_VALUE).
        final long id = superRoot.topNodeId == 0 ? secondOrdinal : superRoot.topNodeId + 1;
        TopNode newSuperRoot = new TopNode(id, newRoot, accessData, time, Spos.NULL);
        final int h = newSuperRoot.pointersLength;
        
        nodeChangeListener.topNodeCreated(newSuperRoot);
        nodeChangeListener.topNodeReplaced(superRoot);  // it existed before this transaction
        pointerCreationListener.pointerCreated(newSuperRoot, 0, newRoot);
        Pointer inherited = new Pointer();
        
        for (int i = 0; i < h; i++) {
            if ((id & TopNode.power2(i)) != 0) {
                assert superRoot != null;
                assert superRoot.pointers != null;
                
                TopNode pointer = null;
                long pointerPos = Spos.NULL;
                
                if (i < superRoot.pointersLength) {
                    superRoot.getPointer(i + 1, inherited);
                    pointer = (TopNode) inherited.node;
                    pointerPos = inherited.pos;
                }

                if (pointer == null && pointerPos != Spos.NULL) {
                    // A stream pointer, as after a restart: inherited like a memory
                    // pointer, so that the skip list does not depend on the pointer form.
                    newSuperRoot.pointers[i] = null;
                    newSuperRoot.pointersPos[i] = pointerPos;
                    newSuperRoot.pointersTime[i] = superRoot.pointersTime[i];
                    continue;
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
     * Finds the space root node for a given lookup time.
     * Returns null if there is no space root that is old enough.
     * 
     * @param accessData Access data for this access.
     */
    public final KeyNode findRoot(long time, OpData op) {
        TopNode n = findSuperRootAtTime(time, op);
        if (n == null) {
            return null;
        }
        return (KeyNode) op.followPointer(n, 0);
    }
    
    /**
     * Finds the top node that was super root node at a given time.
     * Returns null if there is no accessible top node that was 
     * super root at the given time.
     * 
     * @param accessData Access data for this access.
     */
    public final TopNode findSuperRootAtTime(long time, OpData op) {
        //
        // 130123 Frans: Fixed concurrency bug.
        // The volatile read in the beginning of this method is important. It makes memory writes
        // by writer visible and it makes sure we are using the same superRoot instance
        // throughout this method. this.superRoot can change concurrently.
        //
        
        TopNode mySuperRoot = this.superRoot;     // volatile read make writes visible.
        
        op.pointerListener.superRootAccessed(mySuperRoot);
        
        if (time >= mySuperRoot.rootTime) {
            return mySuperRoot;
        }
        
        TopNode n = mySuperRoot;
        
        // Finds right-most pointer with time >= 'time'.
        
        Pointer pt = op.tempPointer;
        
        while (true) {
            rightMostGte(n, time, pt);
            if (pt.isNull()) {
                break;
            }
            
            n = (TopNode) op.followPointer(n, pt.index);
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
        
        TopNode n2 = (TopNode) op.followPointer(n, pt.index);
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
}
