package bergdb.graph;

import bergdb.common.Bug;
import bergdb.common.Bytes;
import bergdb.common.Pair;
import bergdb.common.Util;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
import bergdb.storage.StreamFormatException;

/**
 * A ValueNode is an INode that contains the value of the KV in the database.
 * The internal byte[] value is immutable.
 * 
 * @author Frans Lundberg
 */
public final class ValueNode implements INode {
    private final byte[] value;
        // Synch note: final - no problem.
    public volatile long spos;
        // Synch note: "volatile" needed here to publish writes. Should not affect performance much.
        // Seldom written (when written to stream or read from stream). Reads are more common.
        // Reads of volative are noop on x86, I heard.
    public boolean isInTransactionNodes = false;
        // Synch note: this field must only be accessed from threads holding DB.writeLock.
    
    /**
     * Creates a new delete ValueNode (value == null).
     */
    public ValueNode() {
        this.value = null;
        this.spos = Spos.NULL;
    }
    
    public ValueNode(byte[] value) {
        this.value = value;
        this.spos = Spos.NULL;
    }
    
    public final byte getType() {
        return TYPE_VALUE;
    }
    
    public final boolean isTopOrKeyNode() {
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
     * called with b == true, an IllegalArgumentException is thrown.
     */
    public final void setIsDirty(boolean b) {
        if (b == true) {
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

    public final int getByteSize(int choicesSize) {
        return value == null ? 
                  8 + 2 + choicesSize 
                : 8 + 4 + value.length + 2 + choicesSize;
    }
    
    /**
     * The value is serialized to the byte buffer.
     */
    public final int toBytes(Choices choices, byte[] buffer, final int firstOffset) {
        int offset = firstOffset;
        int byteSize = getByteSize(choices.size);
        long myLong;
        long nodeType = value == null ? INode.TYPE_DELETE : INode.TYPE_VALUE;
        
        myLong = ((long)byteSize) | (nodeType << (4*8)) | (1L << (5*8));
        Bytes.longToBytesLE(myLong, buffer, offset);  offset += 8;
            // Room for 2 checksum bytes.
        
        if (nodeType == TYPE_VALUE) {
            Bytes.intToBytesLE(value.length, buffer, offset);
            offset += 4;
            
            System.arraycopy(value, 0, buffer, offset, value.length);
            offset += value.length;
            
            if (choices.size > Short.MAX_VALUE) {
                throw new Bug("Bad size of choices, " + choices.size);
            }
            Bytes.shortToBytesLE((short) choices.size, buffer, offset);
            offset += 2;
            System.arraycopy(choices.choices, 0, buffer, offset, choices.size);
            offset += choices.size;
        } else {
            // For a TYPE_DELETE, only choices are written, we have no value.
            if (choices.size > Short.MAX_VALUE) {
                throw new Bug("Bad size of choices, " + choices.size);
            }
            Bytes.shortToBytesLE((short) choices.size, buffer, offset);
            offset += 2;
            System.arraycopy(choices.choices, 0, buffer, offset, choices.size);
            offset += choices.size;
        }
        
        // Checksum, XOR of all bytes to buffer[firstOffset + 6], 0 -> 1. 0 used as no checksum indicator.
        
        int checksum = 0;
        for (int i = 0; i < byteSize; i++) {
            checksum ^= buffer[firstOffset + i];
        }
        checksum = checksum & 0x000000ff;
        checksum = checksum == 0 ? 1 : checksum;
        buffer[firstOffset + 6] = (byte) checksum;
        
        assert offset - firstOffset == byteSize;
        return byteSize;
    }
    
    /**
     * @throws StreamFormatException
     */
    public static ValueNode fromBytes(byte[] buffer, int offset, long spos) {
        assert buffer != null;
        assert buffer.length > offset;
        
        offset += 4;         // Skips byte size.
        byte type = buffer[offset];
        offset += 1;
        if (type != INode.TYPE_VALUE && type != INode.TYPE_DELETE) {
            throw new Bug("Bad node type byte, " + ((int) type) 
                    + ", should have been checked already.");
        }
        
        ValueNode result;
        
        if (type == INode.TYPE_DELETE) {
            byte version = buffer[offset];
            offset += 1;
            
            if (version != 1) {
                throw new StreamFormatException("Can only handle ValueNode of " +
                        "version 1, got version " + version + ".");
            }
            
            result = new ValueNode();
        } else {
            byte version = buffer[offset];
            offset += 1;
            
            if (version != 1) {
                throw new StreamFormatException("Can only handle ValueNode of " +
                        "version 1, got version " + version + ".");
            }
            
            offset += 2;   // two bytes not used
            
            int size = Bytes.bytesToIntLE(buffer, offset);
            offset += 4;
            
            byte[] value = new byte[size];
            System.arraycopy(buffer, offset, value, 0, size);
            
            result = new ValueNode(value);
        }
        
        result.spos = spos;
        
        return result;
    }
    
    /**
     * @throws StreamFormatException
     */
    public static Pair<ValueNode, byte[]> fromBytesIncludingChoices(byte[] buffer, int offset, long spos) {
        assert buffer != null;
        assert buffer.length > offset;
        
        offset += 4;         // Skips byte size.
        byte type = buffer[offset];
        offset += 1;
        if (type != INode.TYPE_VALUE && type != INode.TYPE_DELETE) {
            throw new Bug("Bad node type byte, " + ((int) type) 
                    + ", should have been checked already.");
        }
        
        Pair<ValueNode, byte[]> result;
        
        if (type == INode.TYPE_DELETE) {
            byte version = buffer[offset];
            offset += 1;
            
            if (version != 1) {
                throw new StreamFormatException("Can only handle ValueNode of " +
                        "version 1, got version " + version + ".");
            }
            
            short size = Bytes.bytesToShortLE(buffer, offset);
            offset += 2;
            byte[] choices = new byte[size];
            System.arraycopy(buffer, offset, choices, 0, size);
            offset += size;
            
            ValueNode valueNode = new ValueNode(null);
            valueNode.spos = spos;
            result = new Pair<ValueNode, byte[]>(valueNode, choices);
        } else {
            byte version = buffer[offset];
            offset += 1;
            
            if (version != 1) {
                throw new StreamFormatException("Can only handle ValueNode of " +
                        "version 1, got version " + version + ".");
            }
            
            offset += 2;   // two bytes not used
            
            int size = Bytes.bytesToIntLE(buffer, offset);
            offset += 4;
            
            byte[] value = new byte[size];
            System.arraycopy(buffer, offset, value, 0, size);
            offset += size;
            
            size = Bytes.bytesToShortLE(buffer, offset);
            offset += 2;
            byte[] choices = new byte[size];
            try {
                System.arraycopy(buffer, offset, choices, 0, size);
            } catch (ArrayIndexOutOfBoundsException e) {
                throw new ArrayIndexOutOfBoundsException(e.getMessage() + "; size=" + size + ", buffer.length=" + buffer.length + ", offset=" + offset);
            }
            offset += size;
            
            ValueNode valueNode = new ValueNode(value);
            valueNode.spos = spos;
            result = new Pair<ValueNode, byte[]>(valueNode, choices);
        }
        
        return result;
    }
    
    /**
     * The implementation in this class returns 0.
     */
    public final int getMemoryPointerCount() {
        return 0;
    }

    public final long getId() {
        return spos;
    }

    public final void setId(long id) {
        this.spos = id;
    }
    
    public final boolean isDelete() {
        return value == null;
    }
    
    public String print() {
        return toString();
    }
    
    public String toString() {
        String addressString = super.toString();
        String classname = ValueNode.class.getName();
        if (addressString.startsWith(classname)) {
            String sub = addressString.substring(classname.length());
            if (sub.length() > 5) {
                sub = sub.substring(sub.length() - 2);
            }
            addressString = "@" + sub;
        }
        
        String result = "V" + addressString + " " + this.spos + " ";
        
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
                    result = Util.toHexString(value);
                } else {
                    result = Util.toHexString(value, 0, 10) + "...(" + value.length + ")";
                }
            }
        }
        return result;
    }

    /**
     * Always returns 0 since there are no outbound pointers from a ValueNode.
     */
    public final int getPointerCount() {
        return 0;
    }

    /**
     * This method should never be called. Always throws a Bug.
     */
    public void getPointer(int index, Pointer pointer) {
        throw new Bug("A ValueNode has no pointers, " + this.toString());
    }
    
    public INode getPointerNode(int index) {
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
    public void setPointer(int index, INode node, long spos) {
        throw new Bug("A ValueNode has no pointers to set, " + this.toString());
    }

    /**
     * Always returns 'null'.
     */
    public final INode getEvictPointer(int rand) {
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
    
    // ---- Testing ----
    
    @T
    public static void testToBytes() {
        byte[] value = new byte[10];
        value[3] = 3;
        value[9] = -2;
        
        ValueNode node = new ValueNode(value);
        byte[] buffer = new byte[node.getByteSize(0)];
        node.toBytes(new Choices(), buffer, 0);
        
        ValueNode node2 = ValueNode.fromBytes(buffer, 0, Spos.NULL);
        Assert.assertEquals(node.getByteSize(0), node2.getByteSize(0));
        Assert.assertArrayEquals(node.value, node2.value);
    }
    
    @T
    public static void testDummy() {
        // Mostly just to "mark" methods as tested.
        
        ValueNode v = new ValueNode();
        
        Assert.assertEquals(0, v.getPointerCount());
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
}

/*
130118 Frans. Considering concurrency issues carefully.



*/