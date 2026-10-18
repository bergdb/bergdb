package bergdb.dag;

import java.io.PrintStream;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;


/**
 * A TopNode is a node in the data structure (a type of Skip List) 
 * used to find the space root node given a lookup time.
 * 
 * @author Frans Lundberg
 */
public final class TopNode implements Node {
    public final TopNode[] pointers;
        // Backward pointers in skip list.
    public final long[] pointersPos;     
        // stream pos when pointers[x] == null and accessTime when pointers[x] != null.
    public final long[] pointersTime;
        // The rootTime of each skip pointer's target, cached here so that a search can choose
        // a pointer without following it (TopDs.findSuperRootAtTime); -1 for an unused slot.
        // Set when the top node is made (TopDs.newSuperRoot) and kept when it is written and
        // read (StoredTopNode). Not the time the pointer or its target was written.
    final short pointerCount;
        // Same as pointers.length + 1.
    public final short pointersLength;
        // Same as pointers.length.
    
    public KeyNode rootPointer;    // pointer to current space root
    public long rootPointerPos;    // stream pointer corresponding to rootPointer.
    public long rootTime;
    
    public final int topNodeId;
    public volatile long spos;
    public volatile long id = Spos.NULL;
        // The original spos of the node functions as its id.
        // Synch note: made volatile. Not accessed often, does not affect performance.
        // May be removed in future versions. For debug only.
    public boolean isInTransNodes;
        // Synch note: protected by Db.writeLock.
    public int countedMemSize = 0;
        // The size the resident registry counted this canonical object with, 0 if not counted
        // (bergdb item 001, WP J1; core/Residents.java).
    public boolean isDirty = false;
    public boolean isCanonical = false;     // See Node.isCanonical().
        // Synch note: access from threads holding Db.writeLock only.
    
    private static final int MAX_HEIGHT = 30;
    
    /**
     * This constructor should only be called from TopDs, from this class itself,
     * and when parsing a top node.
     */
    public TopNode(int topNodeId, KeyNode rootPointer, long rootPointerPos, long rootTime, long spos) {
        this.rootPointer = rootPointer;
        this.rootPointerPos = rootPointerPos;
        this.rootTime = rootTime;
        
        final int h = height(topNodeId);
        pointers = new TopNode[h];
        pointersPos = new long[h];
        pointersTime = new long[h];
        
        assert pointers.length < Short.MAX_VALUE - 1;
        pointersLength = (short) pointers.length;
        pointerCount = (short) (pointers.length + 1);
        
        this.spos = spos;
        this.topNodeId = topNodeId;
        
        for (int i = 0; i < h; i++) {
            pointers[i] = null;
            pointersPos[i] = Spos.NULL;
            pointersTime[i] = -1;
        }
    }
    
    /**
     * Useful for testing only. Since 2026-10-16 (bergdb item 001, WP A3), with the skip
     * pointers that a top node with this ordinal has in a database (TopDs.newSuperRoot):
     * one at each set bit of the ordinal, here a stream pointer to a made-up position,
     * since StoredTopNode.parse refuses a top node whose skip pointers do not fit its
     * ordinal.
     */
    public static TopNode createDummy(int topNodeId) {
        long keyNodeSpos = 100;
        
        KeyNode k = new KeyNode();
        k.setSpos(keyNodeSpos);
        k.setId(keyNodeSpos);
        
        TopNode result = new TopNode(topNodeId, k, k.getSpos(), 1, 100);
        result.setId(103);
        for (int i = 0; i < result.pointersLength; i++) {
            if ((topNodeId & power2(i)) != 0) {
                result.pointersPos[i] = 16 * (i + 1);
                result.pointersTime[i] = 0;
            }
        }
        
        return result;
    }
    
    public int getTopNodeId() {
        return topNodeId;
    }
    
    public final byte getType() {
        return Node.TYPE_TOP_NODE;
    }
    
    public final boolean isIndexNode() {
        return true;
    }
    
    public long getRootTime() {
        return rootTime;
    }
    
    private static int height(int id) {
        //
        // power2: 1  2  4  8
        //      i: 0  1  2  3
        //
        
        if (id > TopNode.MAX_TOP_NODE_ID_VALUE) {
            throw new IllegalStateException("Bad id value: " + id);
        }
        
        int i = 0; 
        for (i = 0; i < MAX_HEIGHT; i++) {
            if (id < power2(i)) {
                break;
            }
        }
        return i;
    }
    
    /** Maximum supported value of a TopNode id. */
    public static final int MAX_TOP_NODE_ID_VALUE = power2(MAX_HEIGHT) - 1;
    
    public static final int power2(int x) {
        return 1 << x;
    }
    
    private static final String CLASSNAME = TopNode.class.getName();
    
    public String toString() {
        String s = super.toString();
        if (s.startsWith(CLASSNAME)) {
            String sub = s.substring(CLASSNAME.length());
            if (sub.length() > 5) {
                sub = sub.substring(sub.length() - 2);
            }
            s = sub;
        }
        
        String midPart = (id == -1 && spos == -1) ? " " : " " + id + ":" + spos + " ";
        //String result = "T" + topNodeId + "/" + s + midPart + "t=" + rootTime;
        String result = "T" + topNodeId + midPart + "t=" + rootTime;
        return result;
    }
    
    public void printGraph(PrintStream out, String indent, int depth) {
        // A nice refactoring could be to use some kind of iterator / visitor
        // to separate the printing from the iteration.
        
        TopNode topNode;
        String newIndent = "    " + indent;
        
        out.println(indent + this.toString() + " -->");
        
        for (int i = pointersLength - 1; i >= 0; i--) {
            topNode = pointers[i];
            
            if (topNode == null) {
                out.println(indent + "-->" + pointersPos[i]);
            } else {
                topNode.printGraph(out, newIndent, depth + 1);
            }
        }
        
        KeyNode rootNode = this.rootPointer;
        
        if (rootNode == null) {
            out.println(newIndent + "root node spos: " + rootPointerPos);
        } else {
            rootNode.printInternal(out, newIndent, depth + 1, true);
            out.flush();
        }
    }

    public long getSpos() {
        return spos;
    }

    public void setSpos(long spos) {
        this.spos = spos;
    }
    
    public final int getMemSize() {
        // 
        // * 16 - overhead of this object.
        // * 48 - fields
        // * 3*16 - overhead of three array objects.
        // * 3*8*arrayLength - overhead for three arrays. 
        // The arrays are all assumed to be pointers.length long.
        //
        
        return 112 + pointersLength * 24;
    }

    public int getMemoryPointerCount() {
        int count = rootPointer == null ? 0 : 1;
        
        for (int i = 0; i < pointersLength; i++) {
            if (pointers[i] != null) {
                count++;
            }
        }
        return count;
    }

    public long getId() {
        return id;
    }

    public final void setId(long id) {
        this.id = id;
    }

    public final boolean isInTransNodes() {
        return isInTransNodes;
    }

    public final boolean isCanonical() {
        return isCanonical;
    }
    
    public final void setCanonical(boolean isCanonical) {
        this.isCanonical = isCanonical;
    }

    public final void setIsInTransNodes(boolean b) {
        this.isInTransNodes = b;
    }
    
    public final boolean isDirty() {
        return this.isDirty;
    }
    
    public final void setDirty(boolean isDirty) {
        this.isDirty = isDirty;
    }

    public final int getSize() {
        return pointerCount;
    }
    
    public final int getSizeAtTime(long lookupTime) {
        return getSize();
    }

    /**
     * Gets the pointer as one coherent pair (node, pos); see KeyNode.getPointer(). The
     * reference is read once, and a memory pointer is decided on that read (bergdb item 001,
     * WP R8, change 4: M24 of docs/level4-alignment.md). Before 2026-10-17 it was tested and
     * then read again, which, once eviction can clear it in between, gives a null node with
     * access data for its position.
     */
    public final void getPointer(final int index, Pointer pointer) {
        pointer.index = index;
        
        final Node n = index == 0 ? rootPointer : pointers[index - 1];
        if (n != null) {
            pointer.node = n;
            pointer.pos = index == 0 ? rootPointerPos : pointersPos[index - 1];
            return;
        }

        synchronized (this) {
            if (index == 0) {
                pointer.node = rootPointer;
                pointer.pos = rootPointerPos;
            } else {
                pointer.node = pointers[index - 1];
                pointer.pos = pointersPos[index - 1];
            }
        }
    }
    
    public final long getPointerTime(int index) {
        return index == 0 ? rootTime : pointersTime[index - 1];
    }
    
    public final Node getPointerNode(int index) {
        return index == 0 ? rootPointer : pointers[index - 1];
    }
    
    public final long getPointerPos(int index) {
        return index == 0 ? rootPointerPos : pointersPos[index - 1];
    }
    
    public final void setPointer(int index, Node node, long spos) {
        synchronized (this) {   // See getPointer().
            if (index == 0) {
                rootPointer = (KeyNode) node;
                rootPointerPos = spos;
            } else {
                index -= 1;
                pointers[index] = (TopNode) node;
                pointersPos[index] = spos;
            }
        }
    }
    
    /**
     * Sets the access data of a memory pointer, and leaves a stream pointer's position as it
     * is; see KeyNode.setPointerAccessData() (bergdb item 001, WP R8, change 4: M23, M24;
     * before 2026-10-17 it asserted a memory pointer and wrote always). The caller holds the
     * pointer's lock.
     */
    public final void setPointerAccessData(int index, long accessData) {
        if (index == 0) {
            if (rootPointer != null) {
                rootPointerPos = accessData;
            }
        } else {
            index -= 1;
            if (pointers[index] != null) {
                pointersPos[index] = accessData;
            }
        }
    }
    
    /** The access data of a memory pointer; Spos.NULL for a stream pointer. */
    public final long getPointerAccessData(int index) {
        if (index == 0) {
            return rootPointer != null ? rootPointerPos : Spos.NULL;
        } else {
            index -= 1;
            return pointers[index] != null ? pointersPos[index] : Spos.NULL;
        }
    }
    
    public void accept(NodeVisitor visitor) {
        visitor.visit(this);
    }
    
    public String print() {
        return print("");
    }
    
    public String print(String indent) {
        return indent + toString() + "\n";
    }

    
    // ======== Tests ========
    
    @Nano
    public static void testHeight1() {
        Assert.assertEquals(0, TopNode.height(0));
        Assert.assertEquals(1, TopNode.height(1));
        Assert.assertEquals(2, TopNode.height(2));
        Assert.assertEquals(2, TopNode.height(3));
        Assert.assertEquals(3, TopNode.height(4));
        Assert.assertEquals(3, TopNode.height(5));
        Assert.assertEquals(3, TopNode.height(6));
        Assert.assertEquals(3, TopNode.height(7));
        Assert.assertEquals(4, TopNode.height(8));
        Assert.assertEquals(4, TopNode.height(9));
        Assert.assertEquals(4, TopNode.height(10));
    }
    
    @Nano
    public static void testHeight2() {
        //Assert.assertEquals(10, TopNode.height(1023));
        //Assert.assertEquals(11, TopNode.height(1024));
        //Assert.assertEquals(11, TopNode.height(1025));
        //Assert.assertEquals(7, TopNode.height(100));   // 64 = 2^6
        //Assert.assertEquals(20+1, TopNode.height(1024*1024));
        Assert.assertEquals(30, TopNode.height(1024*1024*1024 / 2));
    }

    public boolean isKeyNode() { return false; }
    public boolean isTopNode() { return true; }
    public boolean isValueNode() { return false; }
}
