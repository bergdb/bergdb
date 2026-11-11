package bergdb.core;

import bergdb.common.Bug;
import bergdb.common.Bytes;
import bergdb.dag.Handle;
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
import bergdb.storage.VersioningStreamException;

/**
 * This class is responsible for how to store a TopNode in the stream:
 * serialization/deserialization.
 * 
 * <p>Format version 3 of record format 7, little-endian, 48 + 16 * h bytes for a top node
 * with h skip pointers (h is the bit length of its ordinal): bytes 0 to 3, the size; 4, the
 * type; 5, the version; 6 and 7, zero; 8 to 11, the checksum (NodeChecksum); 12 to 15, zero;
 * 16, h; 17, zero; 18 to 23, the ordinal, an unsigned 48-bit number (bergdb item 005-02;
 * before it, the ordinal's bytes were read as an int and the ordinal was below 2^30); 24 to
 * 31, the node id; 32 to 39, the root time; 40 to 47, the root pointer's position. Then,
 * for each skip pointer, its position and the time it caches, Spos.NULL and -1 when unset.
 * Skip pointer i is set exactly when bit i of the ordinal is. In version 2, until the
 * checksum's 4 bytes (bergdb 024-25), the node was 40 + 16 * h bytes, the checksum in bytes 6
 * and 7, and every field from h on 8 bytes earlier.</p>
 * 
 * @author Frans Lundberg
 */
public class StoredTopNode implements StoredNode {
    public static final int ID_OFFSET = 24;
    
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
        
        if (version != 3) {
            throw new VersioningStreamException("Cannot parse top node of "
                    + "format version " + version + ".");
        }

        offset += 2; // zero bytes
        offset += NodeChecksum.SIZE + 4; // checksum bytes, checked before parsing; zero bytes
        
        // offset == 16 here

        int pointerCount = buffer[offset];
        offset += 1;
        if (pointerCount < 0) {         // 2026-10-21 (bergdb 005-21), before the arrays
            throw new StreamFormatException("TopNode at " + spos + " with " + pointerCount
                    + " skip pointers.");
        }
        // The node's size is its pointers' (getByteSize), checked before the arrays
        // (2026-11-03, bergdb 015-07): before, only the assert below checked it, after them. A
        // node whose checksum was right but whose count did not fit it read the bytes after
        // it, or threw an ArrayIndexOutOfBoundsException, which escaped the reads' failure
        // handling.
        final int nodeSize = Bytes.bytesToIntLE(buffer, firstOffset);
        if (nodeSize != 48 + 16 * pointerCount || nodeSize > buffer.length - firstOffset) {
            throw new StreamFormatException("TopNode at " + spos + " with " + pointerCount
                    + " skip pointers has the size " + nodeSize + ", not "
                    + (48 + 16 * pointerCount) + ", or more than its buffer.");
        }

        offset += 1; // rest of header (reserved)

        // The ordinal: bytes 18 to 23, an unsigned 48-bit number (bergdb item 005-02,
        // register M46). Before, its first 4 bytes were read as an int, and ordinals were
        // below 2^30; their bytes are the same.
        long topNodeId = Bytes.bytesToLongLE(buffer, firstOffset + 16) >>> 16;
        offset += 6;
        
        // offset == 24 here

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
            if (set != ((topNodeId & (1L << i)) != 0)) {
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
        return 48 + 16 * node.pointersLength;
    }
    
    /**
     * Serializes the node to a long array.
     */
    public static int toLongs(TopNode node, long[] buffer, final int firstOffset) {
        int byteSize = getByteSize(node);
        int offset = firstOffset;
        long l;
        final long FORMAT_VERSION = 3;     // serial format version (one byte)
        
        assert byteSize % 8 == 0 : "byteSize=" + byteSize;

        l = ((long) byteSize) 
                | (((long) Node.TYPE_TOP_NODE) << (4 * 8)) 
                | (FORMAT_VERSION << (5 * 8));
        
        buffer[offset++] = l;
        
        // Bytes 8 to 11, the checksum, zero here: StoredTrans.Serializer sets it in the
        // record's bytes (NodeChecksum, bergdb 024-25). Bytes 12 to 15 are zero.
        buffer[offset++] = 0;

        // 2026-10-16 (bergdb item 001, WP A3; F1-008-13, 5.1): the ordinal is widened before
        // it is shifted. It was shifted as an int, so the stored ordinal was its low 16 bits,
        // and ordinals from 32,768 on were written wrong. Since bergdb item 005-02, the
        // ordinal is a long below 2^48, in bytes 18 to 23; byte 17 stays zero.
        l = ((long) node.pointersLength) | (node.topNodeId << (2 * 8));
        buffer[offset++] = l;

        buffer[offset++] = node.getId();

        buffer[offset++] = node.rootTime;

        // spos value for the pointers

        // Coherent pairs (node, pos): a reader can replace a stream pointer by a memory
        // pointer at any time (TopNode.getPointer(), in getSerializedRef()).
        long spos = node.getSerializedRef(0);
        
        buffer[offset++] = spos;

        for (int i = 0; i < node.pointersLength; i++) {
            spos = node.getSerializedRef(i + 1);
            buffer[offset++] = spos;

            long time = spos == Spos.NULL ? -1 : node.pointersTime[i];
            buffer[offset++] = time;
        }
        
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
    /** bergdb 005-21: a negative skip pointer count is a StreamFormatException. */
    @Nano
    public static void testNegativePointerCount() {
        TopNode top = TopNode.createDummy(5);
        long[] longs = new long[getByteSize(top) / 8];
        toLongs(top, longs, 0);
        byte[] bytes = Bytes.longsToBytesLE(longs);
        bytes[16] = (byte) -3;
        try {
            parse(bytes, 0, 1000);
            throw new AssertionError("no exception");
        } catch (StreamFormatException e) {
            // Expected.
        }
    }
    
    /** A top node of another format version is refused as one (2026-10-25, bergdb 005-40). */
    @Nano
    public static void testRefusesOtherVersion() {
        TopNode top = TopNode.createDummy(5);
        long[] longs = new long[getByteSize(top) / 8];
        toLongs(top, longs, 0);
        byte[] bytes = Bytes.longsToBytesLE(longs);
        Assert.assertEquals(3, bytes[5]);
        bytes[5] = 2;
        try {
            parse(bytes, 0, 1000);
            throw new AssertionError("parsed");
        } catch (VersioningStreamException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("format version 2"));
        }
    }
    
    @Nano
    public static void testStreamPointerTimesKept() {
        KeyNode root = new KeyNode();
        root.setSpos(80);
        TopNode top1 = new TopNode(1, root, 80, 20, 100);
        TopNode top2 = new TopNode(2, root, 80, 30, 200);
        TopNode top3 = new TopNode(3, root, 80, 40, 300);
        top3.setPointer(1, Handle.of(top2), top2.getSpos());
        top3.pointersTime[0] = 30;
        top3.setPointer(2, Handle.of(top1), top1.getSpos());
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
     * except the first and the largest ordinal, which are made directly. Since bergdb item
     * 005-02 also ordinals from 2^30 to the largest, 2^48 - 1.
     */
    @Nano
    public static void testOrdinalsRoundTrip() {
        long[] ordinals = {1, 2, 3, 32767, 32768, 32769, 65535, 65536, 98303, 1 << 20,
                (1L << 30) - 1, 1L << 30, (1L << 31) - 1, 1L << 31, (1L << 32) - 1, 1L << 32,
                (1L << 32) + 5, 1L << 40, (1L << 47) - 1, 1L << 47, (1L << 48) - 2};
        for (long n : ordinals) {
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
        long[][] cases = {{65536, 0}, {98303, 32767}, {5, 4}, {6, 5}, {(1L << 32) + 5, 5},
                {(1L << 40) + 3, 3}};
        for (long[] c : cases) {
            long[] longs = new long[getByteSize(topOfLayout(c[0])) / 8];
            toLongs(topOfLayout(c[0]), longs, 0);
            byte[] bytes = Bytes.longsToBytesLE(longs);
            for (int b = 0; b < 6; b++) {
                bytes[18 + b] = (byte) (c[1] >>> (8 * b));      // The ordinal field.
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
     * The ordinal's bytes (bergdb item 005-02): bytes 18 to 23, little-endian, byte 17 zero
     * (10 to 15 and 9 until bergdb 024-25). An ordinal below 2^30 has the bytes it had when
     * the field was read as an int from its first 4 bytes, with its last 2 bytes zero.
     */
    @Nano
    public static void testOrdinalField() {
        long[] ordinals = {0, 1, 32768, 98303, (1L << 30) - 1, 1L << 30, (1L << 32) + 5,
                (1L << 40) + 3, TopNode.MAX_TOP_NODE_ID_VALUE};
        for (long n : ordinals) {
            TopNode top = topOfLayout(n);
            long[] longs = new long[getByteSize(top) / 8];
            toLongs(top, longs, 0);
            byte[] bytes = Bytes.longsToBytesLE(longs);
            Assert.assertEquals("ordinal " + n + ", byte 16", top.pointersLength, bytes[16]);
            Assert.assertEquals("ordinal " + n + ", byte 17", 0, bytes[17]);
            for (int b = 0; b < 6; b++) {
                Assert.assertEquals("ordinal " + n + ", byte " + (18 + b),
                        (byte) (n >>> (8 * b)), bytes[18 + b]);
            }
            if (n < (1L << 30)) {
                Assert.assertEquals("ordinal " + n + " as an int", n,
                        Bytes.bytesToIntLE(bytes, 18));
                Assert.assertEquals("ordinal " + n + ", byte 22", 0, bytes[22]);
                Assert.assertEquals("ordinal " + n + ", byte 23", 0, bytes[23]);
            }
        }
    }

    /**
     * A top node with ordinal n and the slots of the layout (TopDs.newSuperRoot), as stream
     * pointers: slot k is set when bit k of n is, and names the top node whose ordinal is n
     * with bits 0 to k-1 cleared, minus one.
     */
    private static TopNode topOfLayout(long n) {
        TopNode t = new TopNode(n, null, rootPosOf(n), timeOf(n), posOf(n));
        t.setId(posOf(n));
        for (int k = 0; k < t.pointersLength; k++) {
            if ((n & (1L << k)) != 0) {
                long target = ((n >>> k) << k) - 1;
                t.pointersPos[k] = posOf(target);
                t.pointersTime[k] = timeOf(target);
            }
        }
        return t;
    }

    private static long posOf(long ordinal) { return 1024 + 64L * ordinal; }
    private static long rootPosOf(long ordinal) { return 1032 + 64L * ordinal; }
    private static long timeOf(long ordinal) { return 1000 + 3L * ordinal; }

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
                boolean set = (top.topNodeId & (1L << (i - 1))) != 0;
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
            TopNode older = top1.pointers[i] == null ? null : (TopNode) top1.pointers[i].obj;
            if (older != null && older.getSpos() == Spos.NULL) older.setSpos(posOf(older.topNodeId));
            // In a database the writer's top nodes are canonical: a pointer to one is written
            // with its position (bergdb item 009, step 3a; the record rule).
            if (older != null) older.setCanonical(true);
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
    
    /**
     * A top node whose checksum is right but whose pointer count does not fit its size is
     * refused with a StreamFormatException, before its arrays (2026-11-03, bergdb 015-07).
     * Before: a count one larger read the bytes after the node, which the buffer holds here
     * as in a load, and only the assert after the arrays saw it (with -ea); one of 127 threw
     * an ArrayIndexOutOfBoundsException.
     */
    @Nano
    public static void testRefusesPointerCountBeyondTheNode() {
        TopTester t = new TopTester();
        t.createTestData();
        TopNode top = t.ds1.getSuperRoot();
        final int size = StoredTopNode.getByteSize(top);
        long[] longs = new long[size / 8];
        StoredTopNode.toLongs(top, longs, 0);
        for (int count : new int[] {top.pointersLength + 1, 127}) {
            byte[] buffer = java.util.Arrays.copyOf(Bytes.longsToBytesLE(longs), size + 64);
            buffer[16] = (byte) count;
            String refused = StoredValueNode.parseWithRightChecksum(buffer, size);
            Assert.assertTrue(count + ": " + refused, refused.startsWith("TopNode at")
                    && refused.contains("has the size"));
        }
    }
}
