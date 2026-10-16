package bergdb.core;

import bergdb.common.Bug;
import bergdb.common.Bytes;
import bergdb.dag.AccessData;
import bergdb.dag.Dag;
import bergdb.dag.KeyNode;
import bergdb.dag.Node;
import bergdb.dag.Pointer;
import bergdb.dag.Klong;
import bergdb.dag.Spos;
import bergdb.dag.TopDs;
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

        // 2026-10-16 (bergdb item 001, WP A3; review-13-claude, 2): the skip pointers must
        // fit the ordinal: as many as its height, and set exactly at its set bits, as
        // TopDs.newSuperRoot makes them. Before the fix of toLongs, an ordinal of 65,536 or
        // more with bit 15 clear was read as the ordinal modulo 65,536, with the wrong
        // height, and the database went on without an error.
        if (pointerCount != t.pointersLength) {
            throw new StreamFormatException("TopNode at " + spos + " with ordinal " + topNodeId
                    + " has " + pointerCount + " skip pointers, not " + t.pointersLength + ".");
        }
        for (int i = 0; i < pointerCount; i++) {
            boolean set = positions[i] != Spos.NULL;
            if (set != ((topNodeId & (1 << i)) != 0)) {
                throw new StreamFormatException("TopNode at " + spos + " with ordinal "
                        + topNodeId + ": skip pointer " + i + (set ? " is set" : " is not set")
                        + ", which does not fit the ordinal.");
            }
        }

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

        // 2026-10-16 (bergdb item 001, WP A3; F1-008-13, 5.1): the ordinal is widened before
        // it is shifted. It was shifted as an int, so the stored ordinal was its low 16 bits,
        // and ordinals from 32,768 on were written wrong.
        l = ((long) node.pointersLength) | (((long) node.topNodeId) << (2 * 8));
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

    /**
     * Top node ordinals survive the codec (2026-10-16, bergdb item 001, WP A3; F1-008-13,
     * section 5.1, and its review, review-13-claude, section 2). toLongs shifted the
     * ordinal as an int, so ordinals from 32,768 on were written wrong: refused when bit 15
     * is set, else read as the ordinal modulo 65,536, with the wrong height. The tops are
     * made by TopDs.newSuperRoot from a predecessor that has the slots of the layout,
     * except the first and the largest ordinal, which are made directly.
     */
    @Nano
    public static void testOrdinalsRoundTrip() {
        int[] ordinals = {1, 2, 3, 32767, 32768, 32769, 65535, 65536, 98303, 1 << 20};
        for (int n : ordinals) {
            TopDs ds = new TopDs(topOfLayout(n - 1));
            KeyNode root = new KeyNode();
            root.setSpos(rootPosOf(n));
            root.setId(rootPosOf(n));
            ds.newSuperRoot(timeOf(n), root, AccessData.DEFAULT_ACCESS_DATA,
                    Dag.DO_NOTHING_POINTER_CREATED_LISTENER, Dag.DO_NOTHING_NODE_CHANGE_LISTENER);
            TopNode top = ds.getSuperRoot();
            Assert.assertEquals("ordinal made", n, top.topNodeId);
            top.setSpos(posOf(n));
            top.setId(posOf(n));
            checkRoundTrip(top);
        }
        checkRoundTrip(topOfLayout(0));
        checkRoundTrip(topOfLayout(TopNode.MAX_TOP_NODE_ID_VALUE));
    }

    /**
     * The parser refuses a top node whose slots do not fit its ordinal (2026-10-16, bergdb
     * item 001, WP A3): before the fix of toLongs, ordinal 65,536 was read as 0, and 98,303
     * as 32,767, each with the slots of the true ordinal.
     */
    @Nano
    public static void testParserRefusesSlotsThatDoNotFit() {
        int[][] cases = {{65536, 0}, {98303, 32767}, {5, 4}, {6, 5}};
        for (int[] c : cases) {
            long[] longs = new long[getByteSize(topOfLayout(c[0])) / 8];
            toLongs(topOfLayout(c[0]), longs, 0);
            byte[] bytes = Bytes.longsToBytesLE(longs);
            for (int b = 0; b < 4; b++) {
                bytes[10 + b] = (byte) (c[1] >>> (8 * b));      // The ordinal field.
            }
            boolean refused = false;
            try {
                parse(bytes, 0, posOf(c[0]));
            } catch (StreamFormatException e) {
                refused = true;
            }
            Assert.assertTrue("ordinal " + c[0] + " stored as " + c[1] + " refused", refused);
        }
    }

    /**
     * A top node with ordinal n and the slots of the layout (TopDs.newSuperRoot), as stream
     * pointers: slot k is set when bit k of n is, and names the top node whose ordinal is n
     * with bits 0 to k-1 cleared, minus one.
     */
    private static TopNode topOfLayout(int n) {
        TopNode t = new TopNode(n, null, rootPosOf(n), timeOf(n), posOf(n));
        t.setId(posOf(n));
        for (int k = 0; k < t.pointersLength; k++) {
            if ((n & (1 << k)) != 0) {
                int target = ((n >>> k) << k) - 1;
                t.pointersPos[k] = posOf(target);
                t.pointersTime[k] = timeOf(target);
            }
        }
        return t;
    }

    private static long posOf(int ordinal) { return 1024 + 64L * ordinal; }
    private static long rootPosOf(int ordinal) { return 1032 + 64L * ordinal; }
    private static long timeOf(int ordinal) { return 1000 + 3L * ordinal; }

    /** Writes and parses the node, and compares the ordinal, the slots and their times. */
    private static void checkRoundTrip(TopNode top) {
        long[] longs = new long[getByteSize(top) / 8];
        toLongs(top, longs, 0);
        TopNode read = parse(Bytes.longsToBytesLE(longs), 0, top.getSpos()).getNode();
        String what = "ordinal " + top.topNodeId;
        Assert.assertEquals(what, top.topNodeId, read.topNodeId);
        Assert.assertEquals(what + ", slots", top.pointersLength, read.pointersLength);
        Assert.assertEquals(what + ", time", top.rootTime, read.rootTime);
        Assert.assertEquals(what + ", id", top.getId(), read.getId());
        Pointer p = new Pointer();
        for (int i = 0; i < top.getSize(); i++) {
            top.getPointer(i, p);
            long pos = p.getSposForStream();
            Assert.assertEquals(what + ", slot " + i, pos, read.getPointerPos(i));
            if (i > 0) {
                boolean set = (top.topNodeId & (1 << (i - 1))) != 0;
                Assert.assertTrue(what + ", slot " + i + " set as the bit", set == (pos != Spos.NULL));
                Assert.assertEquals(what + ", time of slot " + i, set ? top.pointersTime[i - 1] : -1,
                        read.pointersTime[i - 1]);
            }
        }
    }

    @Nano
    public static void testTopNodeToLongs2() {
        TopTester t = new TopTester();
        t.createTestData();
        TopNode top1 = t.ds4.getSuperRoot();
        // TopTester's top nodes have no positions, so their skip pointers would be written as
        // unset, which the parser refuses since 2026-10-16 (WP A3). Db gives every top node
        // one (Db.setIdOfNode); so does this test.
        for (int i = 0; i < top1.pointersLength; i++) {
            TopNode older = top1.pointers[i];
            if (older != null && older.getSpos() == Spos.NULL) older.setSpos(posOf(older.topNodeId));
        }
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
