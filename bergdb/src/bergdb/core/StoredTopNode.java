package bergdb.core;

import bergdb.common.Bug;
import bergdb.common.Bytes;
import bergdb.dag.INode;
import bergdb.dag.Klong;
import bergdb.dag.Spos;
import bergdb.dag.StreamChecksumException;
import bergdb.dag.TopNode;
import bergdb.dag.TopTester;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
import bergdb.storage.StreamFormatException;

/**
 * This class is responsible for how to store a TopNode in the stream:
 * serialization/deserialization.
 * 
 * @author Frans Lundberg
 */
public class StoredTopNode implements StoredNode {
    private TopNode node;
    
    private StoredTopNode() {}
    
    
    public final TopNode getNode() {
        return node;
    }
    
    public final long getPrevPos() {
        return Spos.NULL;
    }

    /**
     * Creates a TopNode by parsing the data in the byte buffer.
     * 
     * @param buffer
     *            The byte buffer (read from the database stream).
     * @param firstOffset
     *            Offset into the buffer where the serialized node is stored.
     * @param spos
     *            The stream position of the node.
     * @throws StreamFormatException
     * @throws StreamChecksumException
     */
    public static StoredTopNode parse(byte[] buffer, final int firstOffset, long spos) {
        int offset = firstOffset;
        offset += 4; // Skip size bytes
        byte type = buffer[offset];
        offset += 1;
        if (type != INode.TYPE_TOP_NODE) {
            throw new Bug("Bad node type byte, " + ((int) type)
                    + ", should have been checked already.");
        }

        byte version = buffer[offset];
        offset += 1;
        if (version != 1) {
            throw new StreamFormatException("Can only handle TopNode of "
                    + "version 1, got version " + version + ".");
        }

        offset += 2; // checksum bytes, checked later.

        int pointerCount = buffer[offset];
        offset += 1;

        offset += 1; // rest of header (reserved)

        int topNodeId = Bytes.bytesToIntLE(buffer, offset);
        offset += 4;
        offset += 2; // Added, 2 zero bytes.

        if (topNodeId < 0) {
            throw new StreamFormatException("Bad TopNode ID of TopNode in stream, " + topNodeId);
        }
        if (topNodeId >= TopNode.power2[TopNode.power2.length - 1]) {
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

        // TODO E. consider checksum checking here?

        assert Bytes.bytesToIntLE(buffer, firstOffset) == offset - firstOffset;

        TopNode t = new TopNode(topNodeId, null, rootPointerPos, rootTime, spos);

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

        StoredTopNode result = new StoredTopNode();
        result.node = t;
        
        return result;
    }

    public static final int getByteSize(TopNode node) {
        return 40 + 16 * node.pointersLength;
    }

    /**
     * Serializes the node to a long array.
     */
    public static int toLongs(TopNode node, long[] buffer, final int firstOffset) {
        int byteSize = getByteSize(node);
        int offset = firstOffset;
        long checksum = 0;
        long l;
        assert byteSize % 8 == 0 : "byteSize=" + byteSize;

        l = ((long) byteSize) | (((long) INode.TYPE_TOP_NODE) << (4 * 8)) | (1L << (5 * 8));
        // Room for 2 checksum bytes.
        checksum ^= l;
        buffer[offset++] = l;

        l = ((long) node.pointersLength) | (node.topNodeId << (2 * 8));
        checksum ^= l;
        buffer[offset++] = l;
        // 1 + 2 bytes not used

        checksum ^= node.id;
        buffer[offset++] = node.getId();

        checksum ^= node.rootTime;
        buffer[offset++] = node.rootTime;

        // spos for the pointers

        long spos = node.rootPointer == null ? node.rootPointerPos : node.rootPointer.getSpos();
        checksum ^= spos;
        buffer[offset++] = spos;

        for (int i = 0; i < node.pointersLength; i++) {
            INode pointersNode = node.pointers[i];
            spos = pointersNode == null ? node.pointersPos[i] : pointersNode.getSpos();
            checksum ^= spos;
            buffer[offset++] = spos;

            long time = pointersNode == null ? -1 : node.pointersTime[i];
            checksum ^= time;
            buffer[offset++] = time;
        }

        checksum = 0x000000ff & ((checksum >>> 0) ^ (checksum >>> 8) ^ (checksum >>> 16)
                ^ (checksum >>> 24) ^ (checksum >>> 32) ^ (checksum >>> 40) ^ (checksum >>> 48) ^ (checksum >>> 56));
        checksum = checksum == 0 ? 1 : checksum; // 0 used as "no checksum" indication

        buffer[firstOffset] = buffer[firstOffset] | (checksum << (6 * 8));
        assert (offset - firstOffset) * 8 == byteSize : "offset-firstOffset="
                + (offset - firstOffset) + ", byteSize=" + byteSize;
        return byteSize / 8;
    }
    
    // ======== Tests ========

    @T
    public static void testTopNodeToLongs2() {
        TopTester t = new TopTester();
        t.createTestData();
        TopNode top1 = t.ds4.getSuperRoot();
        int size = StoredTopNode.getByteSize(top1);
        assert size % 8 == 0;
        byte[] bytes = new byte[size];
        long[] longs = new long[size / 8];
        StoredTopNode.toLongs(top1, longs, 0);
        for (int i = 0; i < longs.length; i++) {
            Bytes.longToBytesLE(longs[i], bytes, i * 8);
        }
        TopNode top2 = StoredTopNode.parse(bytes, 0, Spos.NULL).getNode();
        
        Assert.assertEquals(top1.topNodeId, top2.topNodeId);
        Assert.assertEquals(top1.rootTime, top2.rootTime);
    }


    @T
    public static void testTopNodeToLongs1() {
        TopTester t = new TopTester();
        t.createTestData();
        TopNode top1 = t.ds1.getSuperRoot();
        int size = StoredTopNode.getByteSize(top1);
        
        assert size % 8 == 0;
        long[] longs = new long[size / 8];
        
        StoredTopNode.toLongs(top1, longs, 0);
        byte[] bytes = new byte[longs.length * 8];
        for (int i = 0; i < longs.length; i++) {
            Bytes.longToBytesLE(longs[i], bytes, i * 8);
        }
        
        TopNode top2 = StoredTopNode.parse(bytes, 0, Spos.NULL).getNode();
        
        Assert.assertEquals(top1.topNodeId, top2.topNodeId);
        Assert.assertEquals(top1.rootTime, top2.rootTime);
    }
}
