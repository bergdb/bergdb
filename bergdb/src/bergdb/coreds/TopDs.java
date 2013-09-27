package bergdb.coreds;


/**
 * The top data structure is used to find the space root node given
 * the the lookup time for the operation.
 * 
 * @author Frans Lundberg
 */
public class TopDs {
    private volatile TopNode superRoot;
    
    public interface DbForMe {
        public INode followPointer(INode predecessor, int pointerIndex, 
                boolean cache, long accessData, GetData gd);
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
     * Finds the space root node for a given lookup time.
     * Returns null if there is no space root that is old enough.
     * 
     * @param accessPath Adds top nodes to the access path if non-null.
     * The returned node is not added to this access path (it cannot be done, since it is not a
     * TopNode).
     * @param accessData Access data for this access.
     */
    public final KeyNode findRoot(DbForMe db, long time, boolean cache, TopAccessPath accessPath,
            long accessData, GetData gd) {
        //
        // The common case of getting the last space root is treated as a 
        // special case for performance.
        //
        // 130123 Frans: Fixed concurrency bug.
        // The volatile read in the beginning of this method is important. It makes memory writes
        // by writer visible and it makes sure we are using the same superRoot instance
        // throughout this method. this.superRoot can change concurrently.
        //
        
        assert gd != null;
        TopNode mySuperRoot = this.superRoot;     // volatile read make writes visible.
        
        if (accessPath != null) { 
            accessPath.add(mySuperRoot);
        }
        
        if (time >= mySuperRoot.rootTime) {
            return (KeyNode) db.followPointer(mySuperRoot, 0, cache, accessData, gd);
        }
        
        TopNode n = mySuperRoot;
        
        // Finds right-most pointer with time >= 'time'.
        
        Pointer pt = gd.tempPointer;
        
        while (true) {
            rightMostGte(n, time, pt);
            if (pt.isNull()) {
                break;
            }
            
            n = (TopNode) db.followPointer(n, pt.index, cache, accessData, gd);
            
            if (accessPath != null) {
                accessPath.add(n);
            }
        }
        
        if (n.rootTime == time) {            
            return (KeyNode) db.followPointer(n, 0, cache, accessData, gd);
        }
        
        // Find left-most pointer
        
        pt.reset();
        leftMost(n, time, pt);
        
        if (pt.isNull()) {
            return null;  // No old-enough node exists
        }
        
        TopNode n2 = (TopNode) db.followPointer(n, pt.index, cache, accessData, gd);
        assert n2 != null : "n2 is unexpectedly null, n: " + n;
        
        if (accessPath != null) {
            accessPath.add(n2);
        }
        
        return (KeyNode) db.followPointer(n2, 0, cache, accessData, gd);
    }
    
    /**
     * For special internal use.
     * Code mostly copied from findRoot(). 
     */
    public final KeyNode findRootAndRecordChoices(DbForMe db, long time, boolean cache,
            long accessData, GetData gd, Choices choices) {
        TopNode mySuperRoot = this.superRoot;     // volatile read make writes visible.
        
        assert choices.getSize() == 0 : choices.getSize();
        
        if (time >= mySuperRoot.rootTime) {
            choices.add(0);
            return (KeyNode) db.followPointer(mySuperRoot, 0, cache, accessData, gd);
        }
        
        TopNode n = mySuperRoot;
        
        // Finds right-most pointer with time >= 'time'.
        
        Pointer pt = gd.tempPointer;
        
        while (true) {
            rightMostGte(n, time, pt);
            if (pt.isNull()) {
                break;
            }
            
            choices.add(pt.index);
            n = (TopNode) db.followPointer(n, pt.index, cache, accessData, gd);
        }
        
        if (n.rootTime == time) {
            choices.add(0);
            return (KeyNode) db.followPointer(n, 0, cache, accessData, gd);
        }
        
        // Find left-most pointer
        
        pt.reset();
        leftMost(n, time, pt);
        
        if (pt.isNull()) {
            return null;  // No old-enough node exists
        }
        
        choices.add(pt.index);
        TopNode n2 = (TopNode) db.followPointer(n, pt.index, cache, accessData, gd);
        assert n2 != null : "n2 is unexpectedly null, n: " + n;
        
        choices.add(0);
        return (KeyNode) db.followPointer(n2, 0, cache, accessData, gd);
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
    public final KeyNode findRootNEW(DbGraph.DbForMe db, long time, TopAccessPath accessPath, GetData gd) {
        //
        // The common case of getting the last space root is treated as a 
        // special case for performance.
        //
        // 130123 Frans: Fixed concurrency bug.
        // The volatile read in the beginning of this method is important. It makes memory writes
        // by writer visible and it makes sure we are using the same superRoot instance
        // throughout this method. this.superRoot can change concurrently.
        //
        
        assert gd != null;
        TopNode mySuperRoot = this.superRoot;     // volatile read make writes visible.
        
        if (accessPath != null) accessPath.add(mySuperRoot);
        
        if (time >= mySuperRoot.rootTime) {
            if (gd.choices != null) gd.choices.add(0);
            return (KeyNode) db.followPointer(mySuperRoot, 0, gd.cache, gd.accessData, gd);
        }
        
        TopNode n = mySuperRoot;
        
        // Finds right-most pointer with time >= 'time'.
        
        Pointer pt = gd.tempPointer;
        
        while (true) {
            rightMostGte(n, time, pt);
            if (pt.isNull()) {
                break;
            }
            
            if (gd.choices != null) gd.choices.add(pt.index);
            n = (TopNode) db.followPointer(n, pt.index, gd.cache, gd.accessData, gd);
            
            if (accessPath != null) accessPath.add(n);
        }
        
        if (n.rootTime == time) {
            if (gd.choices != null) gd.choices.add(0);
            return (KeyNode) db.followPointer(n, 0, gd.cache, gd.accessData, gd);
        }
        
        // Find left-most pointer
        
        pt.reset();
        leftMost(n, time, pt);
        
        if (pt.isNull()) {
            return null;  // No old-enough node exists
        }
        
        if (gd.choices != null) gd.choices.add(pt.index);
        TopNode n2 = (TopNode) db.followPointer(n, pt.index, gd.cache, gd.accessData, gd);
        assert n2 != null : "n2 is unexpectedly null, n: " + n;
        
        if (accessPath != null) {
            accessPath.add(n2);
        }
        
        if (gd.choices != null) gd.choices.add(0);
        return (KeyNode) db.followPointer(n2, 0, gd.cache, gd.accessData, gd);
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
     * Prints data structure to a string.
     */
    public String print(DbForMe db) {
        StringBuilder b = new StringBuilder();
        TopNode t = this.superRoot;
        
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
                    next = (TopNode) db.followPointer(t, i, false, 0, null);
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