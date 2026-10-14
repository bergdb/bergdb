package bergdb.core;

import bergdb.common.Bug;
import bergdb.common.Bytes;
import bergdb.dag.AccessData;
import bergdb.dag.KeyNode;
import bergdb.dag.Node;
import bergdb.dag.Pointer;
import bergdb.dag.Klong;
import bergdb.dag.Spos;
import bergdb.dag.TopNode;
import bergdb.dag.TopTester;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.storage.StreamFormatException;

/**
 * This class is responsible for how to store a TopNode in the stream:
 * serialization/deserialization.
 * 
 * @author Frans Lundberg
 */
public class StoredTopNode implements StoredNode {
    public static final int ID_OFFSET = 16;
    
    private TopNode node;
    
    private StoredTopNode() {}
        
    public final TopNode getNode() {
        return node;
    }
    
    public final long getPrevPos() {
        return Spos.NULL;
    }
    
    public String toString() {
        return "p:" + getPrevPos() + ", n:" + node.toString();
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
        
        if (type != Node.TYPE_TOP_NODE) {
            throw new Bug("Bad node type byte, " + ((int) type)
                    + ", should have been checked already.");
        }

        byte version = buffer[offset];
        offset += 1;
        
        if (version != 2) {
            throw new StreamFormatException("Cannot parse top node of "
                    + "format version " + version + ".");
        }

        offset += 2; // checksum bytes, checked later.
        
        // offset == 8 here

        int pointerCount = buffer[offset];
        offset += 1;

        offset += 1; // rest of header (reserved)

        int topNodeId = Bytes.bytesToIntLE(buffer, offset);
        offset += 4;
        offset += 2; // Added, 2 zero bytes.
        
        // offset == 16 here

        if (topNodeId < 0) {
            throw new StreamFormatException("Bad TopNode ID of TopNode in stream, " + topNodeId);
        }
        
        if (topNodeId > TopNode.MAX_TOP_NODE_ID_VALUE) {
            throw new StreamFormatException("TopNode ID too large in stream, " + topNodeId);
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

        // NOTE consider checksum checking here?

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
        long l;
        final long FORMAT_VERSION = 2;     // serial format version (one byte)
        
        assert byteSize % 8 == 0 : "byteSize=" + byteSize;

        l = ((long) byteSize) 
                | (((long) Node.TYPE_TOP_NODE) << (4 * 8)) 
                | (FORMAT_VERSION << (5 * 8));
        
        // Room for 2 checksum bytes.
        
        buffer[offset++] = l;

        l = ((long) node.pointersLength) | (node.topNodeId << (2 * 8));
        buffer[offset++] = l;
        // 2 bytes not used

        buffer[offset++] = node.getId();

        buffer[offset++] = node.rootTime;

        // spos value for the pointers

        // Coherent pairs (node, pos): a reader can replace a stream pointer by a memory
        // pointer at any time (TopNode.getPointer()).
        Pointer p = new Pointer();
        node.getPointer(0, p);
        long spos = p.getSposForStream();
        
        buffer[offset++] = spos;

        for (int i = 0; i < node.pointersLength; i++) {
            node.getPointer(i + 1, p);
            spos = p.getSposForStream();
            buffer[offset++] = spos;

            long time = spos == Spos.NULL ? -1 : node.pointersTime[i];
            buffer[offset++] = time;
        }
        
        long checksum = NodeChecksum.sum(buffer, firstOffset, offset - firstOffset);
        buffer[firstOffset] = buffer[firstOffset] | (checksum << (6 * 8));
        
        assert (offset - firstOffset) * 8 == byteSize : "offset-firstOffset="
                + (offset - firstOffset) + ", byteSize=" + byteSize;
        return byteSize / 8;
    }
    
    // ======== Tests ========

    /**
     * A top node read from the stream has its skip pointers as stream pointers. When it
     * is written again, the pointer times must be kept, since TopDs uses them to find
     * the super root for a lookup time. Regression test for a bug found 2026-10-12
     * (level 2): the time was written as -1 for every
     * pointer that was not a memory pointer.
     */
    @Nano
    public static void testStreamPointerTimesKept() {
        KeyNode root = new KeyNode();
        root.setSpos(80);
        TopNode top1 = new TopNode(1, root, 80, 20, 100);
        TopNode top2 = new TopNode(2, root, 80, 30, 200);
        TopNode top3 = new TopNode(3, root, 80, 40, 300);
        top3.setPointer(1, top2, AccessData.DEFAULT_ACCESS_DATA);
        top3.pointersTime[0] = 30;
        top3.setPointer(2, top1, AccessData.DEFAULT_ACCESS_DATA);
        top3.pointersTime[1] = 20;

        TopNode read1 = writeAndRead(top3, 400);    // memory pointers written
        TopNode read2 = writeAndRead(read1, 500);   // stream pointers written

        Assert.assertEquals(200, read1.pointersPos[0]);
        Assert.assertEquals(100, read1.pointersPos[1]);
        Assert.assertEquals(30, read1.pointersTime[0]);
        Assert.assertEquals(20, read1.pointersTime[1]);

        Assert.assertEquals(200, read2.pointersPos[0]);
        Assert.assertEquals(100, read2.pointersPos[1]);
        Assert.assertEquals("time of pointer 0, written again", 30, read2.pointersTime[0]);
        Assert.assertEquals("time of pointer 1, written again", 20, read2.pointersTime[1]);
    }

    private static TopNode writeAndRead(TopNode node, long spos) {
        long[] longs = new long[getByteSize(node) / 8];
        toLongs(node, longs, 0);
        return parse(Bytes.longsToBytesLE(longs), 0, spos).getNode();
    }

    @Nano
    public static void testTopNodeToLongs2() {
        TopTester t = new TopTester();
        t.createTestData();
        TopNode top1 = t.ds4.getSuperRoot();
        int size = StoredTopNode.getByteSize(top1);
        assert size % 8 == 0;
        byte[] bytes = new byte[size];
        long[] longs = new long[size / 8];
        
        StoredTopNode.toLongs(top1, longs, 0);
        bytes = Bytes.longsToBytesLE(longs);
        TopNode top2 = StoredTopNode.parse(bytes, 0, Spos.NULL).getNode();
        
        Assert.assertEquals(top1.topNodeId, top2.topNodeId);
        Assert.assertEquals(top1.rootTime, top2.rootTime);
    }


    @Nano
    public static void testTopNodeToLongs1() {
        TopTester t = new TopTester();
        t.createTestData();
        TopNode top1 = t.ds1.getSuperRoot();
        int size = StoredTopNode.getByteSize(top1);
        
        assert size % 8 == 0;
        long[] longs = new long[size / 8];
        
        StoredTopNode.toLongs(top1, longs, 0);
        byte[] bytes = Bytes.longsToBytesLE(longs);
        
        TopNode top2 = StoredTopNode.parse(bytes, 0, Spos.NULL).getNode();
        
        Assert.assertEquals(top1.topNodeId, top2.topNodeId);
        Assert.assertEquals(top1.rootTime, top2.rootTime);
    }
}
