package bergdb.graph;

import java.io.PrintStream;

import bergdb.common.Bug;
import bergdb.common.Bytes;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
import bergdb.storage.StreamFormatException;


/**
 * A TopNode is a node in the data structure (a type of Skip List) 
 * used to find the root space root node given a lookup time.
 * 
 * @author Frans Lundberg
 */
public final class TopNode implements INode {
    public final TopNode[] pointers;
        // Backward pointers in skip list.
    public final long[] pointersPos;     
        // stream pos when pointers[x] == null and accessTime when pointers[x] != null.
    final long[] pointersTime;
        // Time of pointers. When they were written.
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
    //public volatile boolean isDirty;
        // Synch note: This field is accessed by threads not holding DB.writeLock, so we need
        // field to be volatile to publish writes.
    public boolean isInTransNodes;
        // Synch note: protected by DB.writeLock.
    
    private static final int MAX_HEIGHT = 30;
        
    /** power2[x] = 2^x */
    final static int[] power2;
    
    static {
        power2 = new int[MAX_HEIGHT];
        int num = 1;
        
        for (int i = 0; i < power2.length; i++) {
            power2[i] = num;
            num <<= 1;
        }
    }
    
    /**
     * This constructor should only be called from TopDS and from this class itself.
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
        
        //isDirty = false;
        this.spos = spos;
        this.topNodeId = topNodeId;
        
        for (int i = 0; i < h; i++) {
            pointers[i] = null;
            pointersPos[i] = Spos.NULL;
            pointersTime[i] = -1;
        }
    }
    
    public final byte getType() {
        return INode.TYPE_TOP_NODE;
    }
    
    public final boolean isTopOrKeyNode() {
        return true;
    }
    
    public long getRootTime() {
        return rootTime;
    }
    
    private static final int height(int id) {
        //
        // power2: 1, 2, 4, ...
        //         0  1  2
        //
        int i = 0; 
        for (i = 0; i < power2.length; i++) {
            if (id < power2[i]) {      // 1, 2, 4, ...
                break;
            }
        }
        return i;
    }
    
    //public final boolean isDirty() {
    //    return isDirty;
    //}
    
    //public final void setIsDirty(boolean b) {
    //    this.isDirty = b;
    //}
    
    public String toString() {
        String midPart = (id == -1 && spos == -1) ? " " : " " + id + ":" + spos + " ";
        String result = "topNode" + topNodeId + midPart + "t=" + rootTime;
        //result = isDirty ? result + " D" : result;
        return result;
    }
    
    // NOTE Probably not suitable with this code here.
    public void printGraph(PrintStream out, String indent, int depth) {
        // Oldest top nodes first
        
        
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

    public final int getByteSize() {
        return 40 + 16*pointersLength;
    }
    

    /**
     * Serializes a TopNode to bytes.
     * 
     * @deprecated Use toLongs() instead.
     */
    public int toBytes(final byte[] buffer, final int firstOffset, long prevPos) {
        //
        // Note, we would reduce size in stream by including the number of 
        // pointers instead of writing null pointers that occupy space.
        //
        // prevPos is neglected. This is fine, a TopNode is never dirty, no need for previous
        // spos at database startup.
        //
        
        int byteSize = getByteSize();
        int offset = firstOffset;
        long myLong;
        
        myLong = ((long)byteSize) | (((long)INode.TYPE_TOP_NODE) << (4*8)) | (1L << (5*8));
        Bytes.longToBytesLE(myLong, buffer, offset);  offset += 8;
            // Room for 2 checksum bytes.
        
        assert buffer[firstOffset + 4] == INode.TYPE_TOP_NODE : buffer[firstOffset + 4];
        assert buffer[firstOffset + 5] == 1;

        myLong = ((long) pointersLength) | (topNodeId << (2*8));
        Bytes.longToBytesLE(myLong, buffer, offset);  offset += 8;
            // 1 + 2 zero bytes.
        
        Bytes.longToBytesLE(this.id, buffer, offset);  offset += 8;
        
        Bytes.longToBytesLE(this.rootTime, buffer, offset);  offset += 8;
        
        
        // spos for the pointers
        
        long spos = rootPointer == null ? rootPointerPos : rootPointer.getSpos();
        Bytes.longToBytesLE(spos, buffer, offset);  offset += 8;
        
        for (int i = 0; i < pointersLength; i++) {
            INode pointersNode = pointers[i];
            spos = pointersNode == null ? pointersPos[i] : pointersNode.getSpos();
            Bytes.longToBytesLE(spos, buffer, offset);  offset += 8;
            long time = pointersNode == null ? -1 : pointersTime[i];
            Bytes.longToBytesLE(time, buffer, offset);  offset += 8;
        }
        
        //NodeChecksum.compute2(buffer, firstOffset, byteSize, firstOffset + 6);
        
        assert offset - firstOffset == byteSize;
        return byteSize;
    }
    
    /**
     * Serializes the node to a long array.
     */
    public int toLongs(long[] buffer, final int firstOffset) {
        int byteSize = getByteSize();
        int offset = firstOffset;
        long checksum = 0;
        long l;
        assert byteSize % 8 == 0: "byteSize=" + byteSize;
        
        l =       ((long)byteSize) 
                | (((long)INode.TYPE_TOP_NODE) << (4*8)) 
                | (1L << (5*8));
            // Room for 2 checksum bytes.
        checksum ^= l;
        buffer[offset++] = l;
        
        l = ((long) pointersLength) | (topNodeId << (2*8));
        checksum ^= l;
        buffer[offset++] = l;
            // 1 + 2 bytes not used
        
        checksum ^= this.id;
        buffer[offset++] = this.id;
        
        checksum ^= this.rootTime;
        buffer[offset++] = this.rootTime;
        
        // spos for the pointers
        
        long spos = rootPointer == null ? rootPointerPos : rootPointer.getSpos();
        checksum ^= spos;
        buffer[offset++] = spos;
        
        for (int i = 0; i < pointersLength; i++) {
            INode pointersNode = pointers[i];
            spos = pointersNode == null ? pointersPos[i] : pointersNode.getSpos();
            checksum ^= spos;
            buffer[offset++] = spos;
            
            long time = pointersNode == null ? -1 : pointersTime[i];
            checksum ^= time;
            buffer[offset++] = time;
        }
        
        checksum = 0x000000ff & 
               ((checksum >>> 0)  ^ (checksum >>> 8)  ^ (checksum >>> 16) ^ (checksum >>> 24)
              ^ (checksum >>> 32) ^ (checksum >>> 40) ^ (checksum >>> 48) ^ (checksum >>> 56));
        checksum = checksum == 0 ? 1 : checksum;    // 0 used as "no checksum" indication
       
        buffer[firstOffset] = buffer[firstOffset] | (checksum << (6*8));
        assert (offset - firstOffset) * 8 == byteSize : "offset-firstOffset=" + (offset - firstOffset) + ", byteSize=" + byteSize;
        return byteSize / 8;
    }
    
    /**
     * Creates a TopNode from the data in the byte buffer.
     * 
     * @param buffer  The byte buffer (read from the database stream).
     * @param firstOffset  Offset into the buffer where the serialized node is stored.
     * @param spos    The stream position of the node.
     * @throws StreamFormatException
     * @throws StreamChecksumException
     */
    public static TopNode fromBytes(byte[] buffer, final int firstOffset, long spos) {
        int offset = firstOffset;
        offset += 4;    // Skip size bytes
        byte type = buffer[offset];
        offset += 1;
        if (type != INode.TYPE_TOP_NODE) {
            throw new Bug("Bad node type byte, " + ((int) type) 
                    + ", should have been checked already.");
        }
        
        byte version = buffer[offset];
        offset += 1;
        if (version != 1) {
            throw new StreamFormatException("Can only handle TopNode of " +
            		"version 1, got version " + version + ".");
        }
        
        offset += 2;     // checksum bytes, checked later.
        
        int pointerCount = buffer[offset];
        offset += 1;
        
        offset += 1;    // rest of header (reserved)
        
        int topNodeId = Bytes.bytesToIntLE(buffer, offset);
        offset += 4;
        offset += 2;     // Added, 2 zero bytes.
        
        if (topNodeId < 0) {
            throw new StreamFormatException("Bad TopNode ID of TopNode in stream, " + topNodeId);
        }
        if (topNodeId >= power2[power2.length - 1]) {
            throw new StreamFormatException("Bad TopNode ID of TopNode in stream, " + topNodeId);
        }
        
        long id = Bytes.bytesToLongLE(buffer, offset);
        offset += 8;
        
        long rootTime = Bytes.bytesToLongLE(buffer, offset);
        offset += 8;
        if (rootTime < Klong.MIN_TIME) {
            throw new StreamFormatException("Time too small, " + rootTime + ".");
        }
        if (rootTime > Klong.MAX_TIME) {
            throw new StreamFormatException("Time too large, " + rootTime + ".");
        }
        
        long rootPointerPos = Bytes.bytesToLongLE(buffer, offset);
        offset += 8;
        if (rootPointerPos < 0) {
            throw new StreamFormatException("Invalid root pointer pos, " + rootPointerPos + ".");
        }
        
        long[] times = new long[pointerCount];
        long[] positions = new long[pointerCount];
        
        for (int i = 0; i < pointerCount; i++) {
            positions[i] = Bytes.bytesToLongLE(buffer, offset);
            offset += 8;
            
            times[i] = Bytes.bytesToLongLE(buffer, offset);
            offset += 8;
        }
        
        //if (!NodeChecksum.isOk2(buffer, firstOffset, offset - firstOffset, firstOffset + 6)) {
        //    throw new StreamChecksumException("Bad checksum for node at spos " + spos + ", offset = " + (firstOffset + 6) + ".");
        //}
        
        assert Bytes.bytesToIntLE(buffer, firstOffset) == offset - firstOffset;
        
        TopNode t = new TopNode(topNodeId, null, rootPointerPos, rootTime, spos);
        
        //t.isDirty = false;
        t.id = id;
        
        for (int i = 0; i < t.pointersLength; i++) {
            long pos = positions[i];
            if (pos == Spos.NULL) {
                t.pointers[i] = null;
                t.pointersPos[i] = Spos.NULL;
                t.pointersTime[i] = -1;
            } else {
                t.pointers[i] = null;
                t.pointersPos[i] = pos;
                t.pointersTime[i] = times[i];
            }
        }
        
        return t;
    }

    public INode getEvictPointer(int rand) {
        assert rand >= 0;
        INode result = null;
        int total = pointersLength + 1;
        
        for (int i = 0; i < total; i++) {
            int index = rand % total;
            if (index == 0) {
                if (rootPointer != null) {
                    result = rootPointer;
                    break;
                }
            } else {
                INode p = pointers[index - 1];
                if (p != null) {
                    result = p;
                    break;
                }
            }
            
            rand++;
        }
        return result;
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

    public final void setIsInTransNodes(boolean b) {
        this.isInTransNodes = b;
    }
    
    

    public final int getPointerCount() {
        return pointerCount;
    }

    public final void getPointer(int index, Pointer pointer) {
        if (index == 0) {
            pointer.node = rootPointer;
            pointer.pos = rootPointerPos;
        } else {
            index -= 1;
            pointer.node = pointers[index];
            pointer.pos = pointersPos[index];
        }
    }
    
    public final long getPointerTime(int index) {
        return index == 0 ? rootTime : pointersTime[index - 1];
    }
    
    public final INode getPointerNode(int index) {
        return index == 0 ? rootPointer : pointers[index - 1];
    }
    
    public final long getPointerPos(int index) {
        return index == 0 ? rootPointerPos : pointersPos[index - 1];
    }
    
    public final void setPointer(int index, INode node, long spos) {
        if (index == 0) {
            rootPointer = (KeyNode) node;
            rootPointerPos = spos;
        } else {
            index -= 1;
            pointers[index] = (TopNode) node;
            pointersPos[index] = spos;
        }
    }
    
    public final void setPointerAccessData(int index, long accessData) {
        if (index == 0) {
            assert rootPointer != null;
            rootPointerPos = accessData;
        } else {
            index -= 1;
            assert pointers[index] != null;
            pointersPos[index] = accessData;
        }
    }
    
    public final long getPointerAccessData(int index) {
        long result;
        if (index == 0) {
            assert rootPointer != null;
            result = rootPointerPos;
        } else {
            index -= 1;
            assert pointers[index] != null;
            result = pointersPos[index];
        }
        return result;
    }
    
    public void accept(NodeVisitor visitor) {
        visitor.visit(this);
    }
    
    public String print() {
        return toString();
    }
    
    @T
    public static void testHeight() {
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
        Assert.assertEquals(10, TopNode.height(1023));
        Assert.assertEquals(11, TopNode.height(1024));
        Assert.assertEquals(11, TopNode.height(1025));
        Assert.assertEquals(7, TopNode.height(100));   // 64 = 2^6
        Assert.assertEquals(20+1, TopNode.height(1024*1024));
        Assert.assertEquals(30, TopNode.height(1024*1024*1024 / 2));
    }
}
