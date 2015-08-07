package bergdb.dag;

import bergdb.common.Bug;
import bergdb.common.Util;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * A ValueNode is an Node that contains the value of the KV in the database.
 * The internal byte[] value is immutable.
 * 
 * @author Frans Lundberg
 */
public final class ValueNode implements Node {
    // NOTE 141024, the Node.TYPE_VALUE/DELETE is confusing!
    // In this class, the value node is considered a delete if value == null.
    
    public final byte[] value;
        // Synch note: final - no problem.
    public volatile long spos;
        // Synch note: "volatile" needed here to publish writes. Should not affect performance much.
        // Seldom written (when written to stream or read from stream). Reads are more common.
        // Reads of volative are noop on x86, I heard.
    public boolean isInTransactionNodes = false;
        // Synch note: this field must only be accessed from threads holding DB.writeLock.
    
    /**
     * Returns a delete value node (value == null, spos = Spos.NULL).
     */
    public static ValueNode createDelete() {
        return new ValueNode(null, Spos.NULL);
    }
    
    /**
     * Creates a new ValueNode with the given value and spos = Spos.NULL.
     */
    public ValueNode(byte[] value) {
        this(value, Spos.NULL);
    }
    
    public ValueNode(byte[] value, long spos) {
        this.value = value;
        this.spos = spos;
    }
    
    public final byte getType() {
        return value == null ? Node.TYPE_DELETE : Node.TYPE_VALUE;
    }
    
    public final boolean isIndexNode() {
        return false;
    }
    
    /**
     * Returns the stream position, spos, of the node.
     */
    public final long getSpos() {
        return spos;
    }

    /**
     * Sets the stream position, spos, of the node.
     */
    public final void setSpos(long spos) {
        // Called from: NodeStream.addNodes (DB.writeLock held) and from NodeStream.bytesToNode
        // when uncached node is read.        
        this.spos = spos;
    }
    
    /**
     * Caller must hold DB.writeLock.
     */
    public final boolean isInTransNodes() {
        return isInTransactionNodes;
    }

    /**
     * Caller must hold DB.writeLock.
     */
    public final void setIsInTransNodes(boolean b) {
        this.isInTransactionNodes = b;
    }

    /**
     * Returns false; a ValueNode cannot be dirty. Every change
     * is written directly to stream and there are no outbound pointers.
     */
    public final boolean isDirty() {
        return false;
    }

    /**
     * A ValueNode is never dirty. This method should not be used. If it is still used and
     * called with isDirty == true, an IllegalArgumentException is thrown.
     */
    public final void setDirty(boolean isDirty) {
        if (isDirty == true) {
            throw new IllegalArgumentException("A ValueNode cannot be dirty.");
        }
    }

    public final byte[] getValue() {
        return value;
    }
    
    public final int getMemSize() {
        //
        // * 16 - this object itself
        // * 24 - fields (rounded up to nearest 8 bytes)
        // * 16 - the array object overhead
        // * value.length - the array data.
        //
        // If value is null, we have 16+24 only.
        //
        return value == null ? 36 : 56 + value.length;
    }

    /**
     * The implementation in this class returns 0.
     */
    public final int getMemoryPointerCount() {
        return 0;
    }

    /**
     * Returns spos; value nodes do not have a read id attribute 
     * distinct from spos.
     */
    public final long getId() {
        return spos;
    }
    
    /**
     * This method does nothing. Value nodes have no id attribute.
     */
    public final void setId(long spos) {
        // TODO D. Investigate: should we throw exception instead?
    }
    
    public final boolean isDelete() {
        return value == null;
    }
    
    public String print() {
        return print("");
    }
    
    public String print(String indent) {
        return indent + toString() + "\n";
    }
    
    public String toString() {
        String addressString = super.toString();
        String classname = ValueNode.class.getName();
        if (addressString.startsWith(classname)) {
            String sub = addressString.substring(classname.length());
            if (sub.length() > 5) {
                sub = sub.substring(sub.length() - 2);
            }
            addressString = "/" + sub;
        }
        
        String result = "V" + addressString + " " + getSpos() + " ";
        
        if (isDelete()) {
            result += "DELETE";
        } else {
            if (value.length < 20 && Util.isPrintableAscii(value)) {
                result += "\"" + Util.toString(value) + "\"";
            } else {
                result += value.length;
            }
        }
        return result;
    }
    
    public String valueString() {
        String result;
        if (isDelete()) {
            result = "DELETE";
        } else {
            if (Util.isPrintableAscii(value)) {
                if (value.length <= 20) {
                    result = "'" + Util.toString(value) + "'";
                } else {
                    result = "'" + Util.toString(value).substring(0, 20) + "...'";
                }
            } else {
                if (value.length <= 10) {
                    result = Util.toHex(value);
                } else {
                    result = Util.toHex(value, 0, 10) + "...(" + value.length + ")";
                }
            }
        }
        return result;
    }

    /**
     * Always returns 0 since there are no outbound pointers from a ValueNode.
     */
    public final int getSize() {
        return 0;
    }
    
    public final int getSizeAtTime(long lookupTime) {
        return getSize();
    }

    /**
     * This method should never be called. Always throws a Bug.
     */
    public void getPointer(int index, Pointer pointer) {
        throw new Bug("A ValueNode has no pointers, " + this.toString());
    }
    
    public Node getPointerNode(int index) {
        throw new Bug("A ValueNode has no pointers, " + this.toString());
    }
    
    public long getPointerPos(int index) {
        throw new Bug("A ValueNode has no pointers, " + this.toString());
    }

    /**
     * This method should never be called. Always throws a Bug.
     */
    public void setPointer(int index, Pointer pointer) {
        throw new Bug("A ValueNode has no pointers to set, " + this.toString());
    }
    
    /**
     * This method should never be called. Always throws a Bug.
     */
    public void setPointer(int index, Node node, long spos) {
        throw new Bug("A ValueNode has no pointers to set, " + this.toString());
    }

    /**
     * Always returns 'null'.
     */
    public final Node getEvictPointer(int rand) {
        return null;
    }

    /**
     * This method should never be called. Always throws a Bug.
     */
    public void setPointerAccessData(int pointerIndex, long time) {
        throw new Bug("A ValueNode has no pointers to set, " + this.toString());
    }
    
    /**
     * This method should never be called. Always throws a Bug.
     */
    public long getPointerAccessData(int pointerIndex) {
        throw new Bug("A ValueNode has no access data, " + this.toString());
    }

    public void accept(NodeVisitor visitor) {
        visitor.visit(this);
    }
    
    
    // ======== Tests ========
    
    @Nano
    public static void testDummy() {
        // Mostly just to "mark" methods as tested.
        
        ValueNode v = ValueNode.createDelete();
        
        Assert.assertEquals(0, v.getSize());
        Assert.assertEquals(0, v.getMemoryPointerCount());
        Assert.assertEquals(true, v.isDelete());
        Assert.assertEquals(false, v.isDirty());
        
        try {
            v.setPointer(0, null);
        } catch (Bug e) {}
        
        try {
            v.getPointer(0, null);
        } catch (Bug e) {}
        
        v.getEvictPointer(0);
        
        try {
            v.getPointerAccessData(0);
        } catch (Bug e) {}
        
        try {
            v.setPointerAccessData(0, 0);
        } catch (Bug e) {}
    }

    public boolean isTopNode() { return false; }
    public boolean isKeyNode() { return false; }
    public boolean isValueNode() { return true; }
}
