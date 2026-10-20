package bergdb.dag;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * A pointer from a Node to another Node. Used to represent both memory pointers and stream pointers.
 * Useful in method calls like Node.getPointer(int index, Pointer p). 
 * Used as output parameter for efficiency. Used in Db.follow(Pointer p).
 * Typically used for temporary storage, method calls, output parameters.
 * Mutable for performance (to avoid memory allocation).
 * Also has some useful static functions to use when the actual object form of a pointer
 * is not used.
 * 
 * @author Frans Lundberg
 */
public class Pointer {
    /** Memory pointer type. */
    public static final int TYPE_MEMORY = 1;
    
    /** Stream pointer type. */
    public static final int TYPE_STREAM = 2;
    
    public Node node;
    public long pos;
    public int index;    // pointer index, not always used
    
    public Pointer() {
        reset();
    }
    
    /**
     * Resets to initial state; the state identical to that of new Pointer().
     */
    public final void reset() {
        node = null;
        pos = Spos.NULL;
        index = -1;
    }

    /**
     * Returns true if the pointer is a memory pointer.
     */
    public final boolean isMem() {
        return node != null;
    }
    
    /**
     * Gets the pos value of the pointer. 
     * Note that this value is a stream position only when isMem() == false
     * and isNull() == false.
     */
    public final long getPos() {
        return pos;
    }
    
    public final Node getNode() {
        return node;
    }
    
    public final boolean isNull() {
        return isNull(node, pos);
    }
    
    /**
     * Returns the spos-value to store in the node stream.
     * This is the pointee's spos for a memory pointer and the pos value
     * for a stream pointer.
     * If the pointer is null (pos == Spos.NULL) this value is returned.
     */
    public long getSposForStream() {
        return isMem() ? node.getSpos() : pos;
    }
    
    public static final boolean isNull(Node node, long pos) {
        return (node == null) && (pos == Spos.NULL);
    }
    
    /**
     * Returns true if this is a memory pointer.
     */
    public static final boolean isMem(Node node) {
        return node != null;
    }
    
    public String toString() {
        if (isNull()) {
            return "null";
        }
        
        if (isMem()) {
            return "mem->" + node.toString();
        } else {
            return "stream->" + pos;
        }
    }
    
    // ======== Tests ========
    
    @Nano
    public static void test1() {
        Pointer p = new Pointer();
        p.pos = 80L;
        p.node = null;
        p.index = -1;
        
        Assert.assertFalse(p.isMem());
        Assert.assertFalse(p.isNull());
        Assert.assertNull(p.getNode());
    }
}
