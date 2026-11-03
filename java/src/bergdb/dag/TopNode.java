package bergdb.dag;

import java.io.PrintStream;
import java.lang.invoke.MethodHandles;
import java.lang.invoke.VarHandle;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;


/**
 * A TopNode is a node in the data structure (a type of Skip List) 
 * used to find the space root node given a lookup time.
 * 
 * <p>Pointers change in place, as a key node's (KeyNode's class comment; 009-02, 3.4): what
 * a pointer holds (rootPointer, pointers[i]) under the node's monitor with a release store,
 * its reference (rootPointerPos, pointersPos[i]) with an opaque store; a reader reads the
 * handle with an acquire (getPointee) and then the reference with an opaque read
 * (getPointerPos), without a lock (bergdb 015-14; before, plain reads and stores).</p>
 * 
 * @author Frans Lundberg
 */
public final class TopNode implements Node {
    public final Handle[] pointers;
        // Backward pointers in skip list: the handles of the top nodes they point to, or
        // null (bergdb item 009, step 3a; before, the top node objects). Synch note: an
        // element changed in place with a release store, read with an acquire (getPointee).
    public final long[] pointersPos;     
        // The skip pointers' references, positions or vpos (since step 3a; before, access
        // data while a pointer was a memory pointer). Synch note: an element changed in
        // place with an opaque store, read with an opaque read (getPointerPos).
    public final long[] pointersTime;
        // The rootTime of each skip pointer's target, cached here so that a search can choose
        // a pointer without following it (TopDs.findSuperRootAtTime); -1 for an unused slot.
        // Set when the top node is made (TopDs.newSuperRoot) and kept when it is written and
        // read (StoredTopNode). Not the time the pointer or its target was written.
    final short pointerCount;
        // Same as pointers.length + 1.
    public final short pointersLength;
        // Same as pointers.length.
    
    public Handle rootPointer;     // the handle of the space root, or null (009, step 3a)
    public long rootPointerPos;    // the root pointer's reference
        // Synch note: as pointers[i] and pointersPos[i], by ROOT and ROOT_REF (015-14).
    public Handle handle;
        // The handle this object is in, or was in (bergdb item 009, step 3a; KeyNode.handle).
    public long rootTime;
    
    public final long topNodeId;
        // The ordinal: 0 for the first top node, then one more for each (TopDs.newSuperRoot).
        // At most MAX_TOP_NODE_ID_VALUE, 2^48 - 1; an int below 2^30 before bergdb item 005-02.
    public volatile long spos;
    public volatile long id = Spos.NULL;
        // The original spos of the node functions as its id.
        // Synch note: made volatile. Not accessed often, does not affect performance.
        // May be removed in future versions. For debug only.
    public boolean isInTransNodes;
        // Synch note: protected by Db.writeLock.
    public int countedMemSize = -1;
        // The size the resident registry counted this object with, -1 if not counted (bergdb
        // item 001, WP J1; item 009, step 3b; core/Residents.java; 0 before bergdb 015-15).
        // Read and written under the object's monitor.
    public boolean isDirty = false;
    public boolean isCanonical = false;     // See Node.isCanonical().
        // Synch note: written by the writer and by an eviction; read plainly by the readers'
        // Handle.usable, where a stale value is harmless (009-02, 3.4).
    
    private static final int MAX_HEIGHT = 48;
    
    /**
     * This constructor should only be called from TopDs, from this class itself,
     * and when parsing a top node.
     */
    public TopNode(long topNodeId, KeyNode rootPointer, long rootPointerPos, long rootTime,
            long spos) {
        // A root object becomes its handle, with its position as the reference (bergdb item
        // 009, step 3a); without one, rootPointerPos is the stream pointer's position.
        this.rootPointer = rootPointer == null ? null : Handle.of(rootPointer);
        this.rootPointerPos = rootPointer == null ? rootPointerPos : rootPointer.getSpos();
        this.rootTime = rootTime;
        
        final int h = height(topNodeId);
        pointers = new Handle[h];
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
    public static TopNode createDummy(long topNodeId) {
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
    
    public final byte getType() {
        return Node.TYPE_TOP_NODE;
    }
    
    public final boolean isIndexNode() {
        return true;
    }
    
    public long getRootTime() {
        return rootTime;
    }
    
    private static int height(long id) {
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
    
    /**
     * Maximum supported value of a TopNode id, 2^48 - 1: the ordinal has 48 bits in the
     * stream (StoredTopNode). Db refuses user transactions just below it (Db.executeInner;
     * bergdb item 005-02). It was 2^30 - 1 before, register M46.
     */
    public static final long MAX_TOP_NODE_ID_VALUE = power2(MAX_HEIGHT) - 1;
    
    public static final long power2(int x) {
        return 1L << x;
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
            topNode = (TopNode) getPointerNode(i + 1);
            
            if (topNode == null) {
                out.println(indent + "-->" + pointersPos[i]);
            } else {
                topNode.printGraph(out, newIndent, depth + 1);
            }
        }
        
        KeyNode rootNode = (KeyNode) getPointerNode(0);
        
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
        int count = 0;
        for (int i = 0; i < pointerCount; i++) {
            if (getPointerNode(i) != null) {
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
     * WP R8, change 4: M24 of bergdb 001-08). Before 2026-10-17 it was tested and
     * then read again, which, once eviction can clear it in between, gives a null node with
     * access data for its position.
     */
    public final void getPointer(final int index, Pointer pointer) {
        pointer.index = index;
        synchronized (this) {
            pointer.node = getPointerNode(index);
            pointer.pos = getPointerPos(index);
        }
    }
    
    /** See Node.getSerializedRef() and Handle.serializedRef(): the record rule. */
    public final long getSerializedRef(int index) {
        Pointee p;
        long ref;
        synchronized (this) {
            p = getPointee(index);
            ref = getPointerPos(index);
        }
        return Handle.serializedRef(p, ref);
    }
    
    public final long getPointerTime(int index) {
        return index == 0 ? rootTime : pointersTime[index - 1];
    }
    
    /** See Node.getPointerNode(): the handle's object if it may serve the pointer. */
    public final Node getPointerNode(int index) {
        Handle h = getPointee(index);       // an acquire, then the rest (bergdb 015-14)
        if (h == null) return null;
        Node o = h.obj;
        return o != null && Handle.usable(o, getPointerPos(index)) ? o : null;
    }
    
    /** Pointer i's reference, with an opaque read, as KeyNode.getPointerPos (015-14). */
    public final long getPointerPos(int index) {
        return index == 0 ? (long) ROOT_REF.getOpaque(this)
                : (long) REFS.getOpaque(pointersPos, index - 1);
    }
    
    /** What pointer i holds, with an acquire, as KeyNode.getPointee (bergdb 015-14). */
    public final Handle getPointee(int index) {
        return index == 0 ? (Handle) ROOT.getAcquire(this)
                : (Handle) HANDLES.getAcquire(pointers, index - 1);
    }
    
    /** Under the node's monitor, with a release store, as KeyNode.setPointee (015-14). */
    public final void setPointee(int index, Pointee pointee) {
        synchronized (this) {
            if (index == 0) {
                ROOT.setRelease(this, (Handle) pointee);
            } else {
                HANDLES.setRelease(pointers, index - 1, (Handle) pointee);
            }
        }
    }
    
    /** Under the node's monitor, with an opaque store, as KeyNode.setRef (015-14). */
    public final void setRef(int index, long ref) {
        synchronized (this) {
            if (index == 0) {
                ROOT_REF.setOpaque(this, ref);
            } else {
                REFS.setOpaque(pointersPos, index - 1, ref);
            }
        }
    }
    
    public final void raiseRef(int index, long ref) {
        synchronized (this) {
            if (Spos.newer(ref, getPointerPos(index))) setRef(index, ref);
        }
    }
    
    public final boolean swizzle(int index, Pointee expected, Pointee pointee) {
        synchronized (this) {
            if (getPointee(index) != expected) return false;
            setPointee(index, pointee);
            return true;
        }
    }
    
    public final void setPointer(int index, Pointee pointee, long ref) {
        synchronized (this) {   // See getPointer(); the reference first (015-14).
            if (index == 0) {
                ROOT_REF.setOpaque(this, ref);
                ROOT.setRelease(this, (Handle) pointee);
            } else {
                index -= 1;
                REFS.setOpaque(pointersPos, index, ref);
                HANDLES.setRelease(pointers, index, (Handle) pointee);
            }
        }
    }
    
    private static final VarHandle ROOT, ROOT_REF;
    private static final VarHandle HANDLES = MethodHandles.arrayElementVarHandle(Handle[].class);
    private static final VarHandle REFS = MethodHandles.arrayElementVarHandle(long[].class);
    static {
        try {
            MethodHandles.Lookup l = MethodHandles.lookup();
            ROOT = l.findVarHandle(TopNode.class, "rootPointer", Handle.class);
            ROOT_REF = l.findVarHandle(TopNode.class, "rootPointerPos", long.class);
        } catch (ReflectiveOperationException e) {
            throw new ExceptionInInitializerError(e);
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
        Assert.assertEquals(31, TopNode.height(1L << 30));
        Assert.assertEquals(33, TopNode.height(1L << 32));
        Assert.assertEquals(48, TopNode.height(1L << 47));
        Assert.assertEquals(48, TopNode.height(MAX_TOP_NODE_ID_VALUE));
        boolean refused = false;
        try {
            TopNode.height(MAX_TOP_NODE_ID_VALUE + 1);
        } catch (IllegalStateException e) {
            refused = true;
        }
        Assert.assertTrue("above the bound", refused);
    }

    @Nano
    public static void testPointerInPlace() {
        // bergdb 015-14: the root pointer and a skip pointer changed in place (raiseRef,
        // swizzle, setPointer) and read as a follow reads them (getPointee, getPointerPos).
        TopNode t = new TopNode(1, null, 200, 5, Spos.NULL);
        Handle a = new Handle(7);
        Handle b = new Handle(7);
        for (int i = 0; i <= 1; i++) {
            t.setPointer(i, a, 200);
            t.raiseRef(i, 100);
            Assert.assertEquals("never lowered", 200, t.getPointerPos(i));
            t.raiseRef(i, 300);
            Assert.assertEquals(300, t.getPointerPos(i));
            Assert.assertEquals(false, t.swizzle(i, b, b));
            Assert.assertEquals(true, t.swizzle(i, a, b));
            Assert.assertEquals(true, t.getPointee(i) == b);
            t.setRef(i, 400);
            Assert.assertEquals(400, t.getPointerPos(i));
        }
        Assert.assertEquals(true, t.rootPointer == b && t.pointers[0] == b);
        Assert.assertEquals(400, t.rootPointerPos);
        Assert.assertEquals(400, t.pointersPos[0]);
    }

    public boolean isKeyNode() { return false; }
    public boolean isTopNode() { return true; }
    public boolean isValueNode() { return false; }
}
