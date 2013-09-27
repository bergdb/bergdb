package bergdb.coreds;

import bergdb.nanotest.Assert;
import bergdb.nanotest.T;

/**
 * A general-purpose pointer class. Used to represent both memory pointers and stream pointers.
 * Useful in method calls like INode.getPointer(int index, Pointer p). (Used as output parameter
 * for efficiency.)
 * Used in DB.follow(Pointer p).
 * Typically used for temporary storage, method calls, output parameters.
 */
public class Pointer {
    public INode node;
    public long pos;
    public int index;    // pointer index, not always used
    
    public Pointer() {
        reset();
    }
    
    /**
     * Resets to initial state, like just after new Pointer().
     */
    public final void reset() {
        node = null;
        pos = Spos.NULL;
        index = -1;
    }
    
    public final boolean isMem() {
        return node != null;
    }
    
    public final long getPos() {
        return pos;
    }
    
    public final INode getNode() {
        return node;
    }
    
    /**
     * Returns true if this object has is not a memory pointer, nor a valid stream pointer.
     */
    public final boolean isNull() {
        return node == null && pos == Spos.NULL;
    }
    
    public static final boolean isNull(INode node, long pos) {
        return node == null && pos == Spos.NULL;
    }
    
    public static final boolean isMem(INode node) {
        return node != null;
    }
    
    @T
    public static void test1() {
        Pointer p = new Pointer();
        p.pos = 1234L;
        p.node = null;
        
        Assert.assertEquals(false, p.isMem());
        Assert.assertNull(p.getNode());
    }
}
