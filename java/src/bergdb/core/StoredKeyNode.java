package bergdb.core;

import bergdb.common.Bug;
import bergdb.common.Bytes;
import bergdb.common.StringUtil;
import bergdb.dag.Node;
import bergdb.dag.KeyNode;
import bergdb.dag.Klong;
import bergdb.dag.Pointer;
import bergdb.dag.Spos;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.storage.StreamFormatException;
import bergdb.storage.VersioningStreamException;

/**
 * This class is responsible for how to store a KeyNode in the stream. Serialization/deserialization
 * and the extra prevPos field.
 * 
 * <p>Format version 3 of record format 7, little-endian, 32 + 16 * n bytes for a key node of
 * n klongs: bytes 0 to 3, the size; 4, the type; 5, the version; 6 and 7, zero; 8 to 11, the
 * checksum (NodeChecksum); 12, the leaf flag, 1 or 0; 13 and 14, n; 15, zero; 16 to 23,
 * prevPos; 24 to 31, the node id; then the n klongs, then their n pointers. In version 2,
 * until the checksum's 4 bytes (bergdb 024-25), the checksum was in bytes 6 and 7, prevPos in
 * 8 to 15, the flag in 16 and n in 17 and 18; the size is the same.</p>
 * 
 * @author Frans Lundberg
 */
public class StoredKeyNode implements StoredNode {
    public static final int ID_OFFSET = 24;
    private KeyNode node;
    private long prevPos;

    private StoredKeyNode() {
    }

    public KeyNode getNode() {
        return node;
    }

    public long getPrevPos() {
        return prevPos;
    }
    
    public String toString() {
        return "p:" + prevPos + ", n:" + node.toString();
    }

    public static int getByteSize(KeyNode node) {
        return 32 + node.size * 16;
    }

    /**
     * Serializes a KeyNode + prevPos to a long[] buffer.
     * 
     * @return The buffer offset after method has run.
     */
    public static int toLongs(KeyNode node, long[] buffer, final int firstOffset, long prevPos) {
        int sz = node.size;
        int byteSize = getByteSize(node);
        int offset = firstOffset;
        final long FORMAT_VERSION = 3;     // serial format version (one byte)

        buffer[offset++] = 
                  ((long) byteSize) 
                | (((long) Node.TYPE_KEY_NODE) << (4 * 8))
                | (FORMAT_VERSION << (5 * 8));
        
        // Bytes 8 to 11, the checksum, zero here: StoredTrans.Serializer sets it in the
        // record's bytes (NodeChecksum, bergdb 024-25). Byte 15 is zero.
        buffer[offset++] = ((long) (node.isSegmentLeaf() ? 1 : 0)) << (4 * 8)
                | ((long) sz) << (5 * 8);
        buffer[offset++] = prevPos;
        buffer[offset++] = node.getId();

        System.arraycopy(node.klongs, 0, buffer, offset, sz);
        assert reservedTimeBitsZero(buffer, offset, sz);
        offset += sz;
        
        for (int i = 0; i < sz; i++) {
            buffer[offset++] = node.getSerializedRef(i);
        }
        
        assert (offset - firstOffset) * 8 == byteSize;
        assert byteSize % 8 == 0;
        return byteSize / 8;
    }

    /**
     * True if no time klong of the 'count' klongs at 'offset' has a reserved bit set
     * (Klong.TIME_RESERVED_BITS; bergdb 024-25, section 12), which parse() refuses.
     */
    private static boolean reservedTimeBitsZero(long[] klongs, int offset, int count) {
        for (int i = offset; i < offset + count; i++) {
            if (Klong.isTime(klongs[i]) && (klongs[i] & Klong.TIME_RESERVED_BITS) != 0) {
                return false;
            }
        }
        return true;
    }

    /**
     * @throws StreamFormatException
     */
    public static StoredKeyNode parse(byte[] buffer, int offset, long spos) {
        // The key count is checked against the node's size (2026-11-03, bergdb 015-07): a node
        // whose checksum was right but whose count did not fit it threw an
        // ArrayIndexOutOfBoundsException, which escaped the reads' failure handling, or read
        // the bytes after it.
        final int nodeSize = Bytes.bytesToIntLE(buffer, offset);
        if (nodeSize < 32 || nodeSize > buffer.length - offset) {
            throw new StreamFormatException("Bad key node size, " + nodeSize + ", at spos "
                    + spos + ".");
        }
        
        offset += 4; // Skip size.
        byte type = buffer[offset];
        offset += 1;
        if (type != Node.TYPE_KEY_NODE) {
            throw new Bug("Bad node type byte, " + ((int) type)
                    + ", should have been checked already.");
        }

        byte version = buffer[offset];
        
        if (version != 3) {
            throw new VersioningStreamException("Cannot parse key node of format version "
                    + version + ".");
        }
        
        offset += 1;

        offset += 2; // zero bytes
        offset += NodeChecksum.SIZE; // checksum bytes, checked before parsing
        
        // offset == 12 here

        if (!(buffer[offset] == 0 || buffer[offset] == 1)) {
            throw new StreamFormatException("Bad second byte, expected 0 or 1, was "
                    + ((int) buffer[offset]) + ".");
        }
        boolean isSegmentLeaf = buffer[offset] == 1;
        offset += 1;

        int size = Bytes.bytesToShortLE(buffer, offset);
        if (size > Short.MAX_VALUE) {
            throw new StreamFormatException("Bad size: " + size + ", spos=" + spos + ".");
        }
        offset += 2;

        // 1 zero byte
        offset += 1;
        
        // offset == 16 here

        long prevPos = Bytes.bytesToLongLE(buffer, offset);
        if (!Spos.isValidOrNull(prevPos)) {
            throw new StreamFormatException("Bad KeyNode, prevPos is illegal: " + prevPos + ".");
        }
        offset += 8;
        
        // offset == 24 here

        long id = Bytes.bytesToLongLE(buffer, offset);
        offset += 8;

        if (size < 0) {
            throw new StreamFormatException("Bad Node size, " + size + ".");
        }
        // The node's size is its count's exactly, getByteSize() (2026-11-06, bergdb 019-32):
        // a count below what the size holds read the pointers from the wrong bytes, and a
        // key klong got a time klong's Spos.NULL; a read met an assert.
        if (nodeSize != 32 + 16 * size) {
            throw new StreamFormatException("Bad key count, " + size + ", of key node at spos "
                    + spos + ", size " + nodeSize + ".");
        }

        long[] klongs = new long[size];
        long[] positions = new long[size];

        for (int i = 0; i < size; i++) {
            klongs[i] = Bytes.bytesToLongLE(buffer, offset);
            offset += 8;
        }

        // Each klong's type, and a key klong's pointer (2026-11-06, bergdb 019-32): a klong of
        // type 2, which no klong has, or a key klong whose pointer was negative, was taken,
        // and a start or a read met an assert of the Core (an AssertionError; without -ea an
        // IllegalStateException). Spos.NULL is allowed, as DbStarter.validateNode allows it.
        for (int i = 0; i < size; i++) {
            positions[i] = Bytes.bytesToLongLE(buffer, offset);
            offset += 8;
            int klongType = Klong.getIntType(klongs[i]);
            if (klongType != Klong.INT_TYPE_TIME && klongType != Klong.INT_TYPE_KEY
                    && klongType != Klong.INT_TYPE_DELETE_BITMAP) {
                throw new StreamFormatException("Bad klong type, " + klongType + ", of klong "
                        + i + " of key node at spos " + spos + ".");
            }
            // A time klong's reserved bits, 56 to 61, are zero (2026-11-12, bergdb 024-25,
            // section 12): no writer sets them (toLongs asserts it), and a damaged one was
            // taken; getTime() ignores them, so reads answered right, but a start with -ea met
            // KeyNode.addKlong's assert, which compares the whole klong with the time.
            if (klongType == Klong.INT_TYPE_TIME
                    && (klongs[i] & Klong.TIME_RESERVED_BITS) != 0) {
                throw new StreamFormatException("Bad time klong, 0x"
                        + Long.toHexString(klongs[i]) + " (bits 56 to 61 not zero), klong " + i
                        + " of key node at spos " + spos + ".");
            }
            if (klongType == Klong.INT_TYPE_KEY && !Spos.isValidOrNull(positions[i])) {
                throw new StreamFormatException("Bad pointer, " + positions[i] + ", of klong "
                        + i + " of key node at spos " + spos + ".");
            }
        }

        KeyNode keyNode = new KeyNode(isSegmentLeaf);
        keyNode.spos = spos;
        keyNode.id = id;

        for (int i = 0; i < size; i++) {
            keyNode.addToEnd(klongs[i], null, positions[i]);
        }

        keyNode.size = keyNode.size; // Synch action to publish writes.

        StoredKeyNode result = new StoredKeyNode();
        result.node = keyNode;
        result.prevPos = prevPos;
        return result;
    }
    
    
    // ======== Tests ========
    
    @Nano
    private static void testSerialize() {
        KeyNode node = new KeyNode();
        long k0 = Klong.createTime(5000);
        long k1 = Klong.createKey(StringUtil.toBytes("key"));
        node.addToEnd(k0, null, Spos.NULL);
        node.addToEnd(k1, null, 1234);
        
        int byteSize = StoredKeyNode.getByteSize(node);
        long[] longBuffer = new long[byteSize / 8];
        int offset = StoredKeyNode.toLongs(node, longBuffer, 0, 200);
        Assert.assertEquals(byteSize / 8, offset);
        
        byte[] byteBuffer = Bytes.longsToBytesLE(longBuffer);
        StoredKeyNode storedNode = StoredKeyNode.parse(byteBuffer, 0, 0);
        
        Assert.assertEquals(node.size, storedNode.node.size);
        Assert.assertEquals(node.getKlong(0), storedNode.node.getKlong(0));
        Assert.assertEquals(node.getKlong(1), storedNode.node.getKlong(1));
        Assert.assertEquals(1234, storedNode.node.getPointerPos(1));
    }
    
    /** A key node of another format version is refused as one (2026-10-25, bergdb 005-40). */
    @Nano
    private static void testRefusesOtherVersion() {
        KeyNode node = new KeyNode();
        node.addToEnd(Klong.createTime(5000), null, Spos.NULL);
        long[] longBuffer = new long[StoredKeyNode.getByteSize(node) / 8];
        StoredKeyNode.toLongs(node, longBuffer, 0, 200);
        byte[] byteBuffer = Bytes.longsToBytesLE(longBuffer);
        Assert.assertEquals(3, byteBuffer[5]);
        byteBuffer[5] = 2;
        
        try {
            StoredKeyNode.parse(byteBuffer, 0, 0);
            throw new AssertionError("parsed");
        } catch (VersioningStreamException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("format version 2"));
        }
    }
    
    /**
     * A key node whose checksum is right but whose key count does not fit it is refused with
     * a StreamFormatException (2026-11-03, bergdb 015-07). Before: a count of 32,767 threw an
     * ArrayIndexOutOfBoundsException; one of 3, one more than the node holds, read the bytes
     * after the node, which the buffer holds here as in a load.
     */
    @Nano
    private static void testRefusesKeyCountBeyondTheNode() {
        KeyNode node = new KeyNode();
        node.addToEnd(Klong.createTime(5000), null, Spos.NULL);
        node.addToEnd(Klong.createKey(StringUtil.toBytes("key")), null, 1234);
        final int size = getByteSize(node);
        long[] longs = new long[size / 8];
        toLongs(node, longs, 0, 200);
        for (int count : new int[] {32767, 3}) {
            byte[] buffer = java.util.Arrays.copyOf(Bytes.longsToBytesLE(longs), size + 64);
            buffer[13] = (byte) count;          // the count, bytes 13 and 14 (toLongs)
            buffer[14] = (byte) (count >>> 8);
            String refused = StoredValueNode.parseWithRightChecksum(buffer, size);
            Assert.assertTrue(count + ": " + refused, refused.startsWith("Bad key count"));
        }
    }
    
    /**
     * A key node whose checksum is right but whose klongs, pointers or count cannot be a
     * node's is refused with a StreamFormatException (2026-11-06, bergdb 019-32): a klong of
     * type 2, a key klong's pointer of -8, and a key count below what the node's size holds
     * (the pointers read from the wrong bytes). Before, each was parsed, and a start or a
     * read met an assert of the Core (harness 6.1, bergdb 018-07).
     */
    @Nano
    private static void testRefusesBadKlongs() {
        KeyNode node = new KeyNode();
        node.addToEnd(Klong.createTime(5000), null, Spos.NULL);
        node.addToEnd(Klong.createKey(StringUtil.toBytes("key")), null, 1234);
        final int size = getByteSize(node);
        long[] longs = new long[size / 8];
        toLongs(node, longs, 0, 200);
        // What changes the node (the offset of an 8-byte field, its new value; or a byte, its
        // xor), and what the message starts with. Klong i is at 32 + 8 * i, its pointer at
        // 48 + 8 * i, the count at 13.
        Object[][] cases = {
            {"byte", 39, 0x80, "Bad klong type"},
            {"long", 56, -8L, "Bad pointer"},
            {"byte", 13, 3, "Bad key count"},
        };
        for (Object[] c : cases) {
            byte[] buffer = Bytes.longsToBytesLE(longs);
            int at = (Integer) c[1];
            if (c[0].equals("byte")) {
                buffer[at] ^= (byte) (int) (Integer) c[2];
            } else {
                Bytes.longToBytesLE((Long) c[2], buffer, at);
            }
            String refused = StoredValueNode.parseWithRightChecksum(buffer, size);
            Assert.assertTrue(c[0] + " at " + at + ": " + refused,
                    refused.startsWith((String) c[3]));
        }
    }
    
    /**
     * A time klong with one of its reserved bits, 56 to 61, set is refused with a
     * StreamFormatException (2026-11-12, bergdb 024-25, section 12); a node with the largest
     * time, Klong.MAX_TIME, is taken. Before, the klong was taken, and a start with -ea met
     * KeyNode.addKlong's assert (CorruptStreamTester's seeds 20775 and 3971451).
     */
    @Nano
    private static void testRefusesBadTimeKlong() {
        for (long time : new long[] {5000, Klong.MAX_TIME}) {
            KeyNode node = new KeyNode();
            node.addToEnd(Klong.createTime(time), null, Spos.NULL);
            node.addToEnd(Klong.createKey(StringUtil.toBytes("key")), null, 1234);
            final int size = getByteSize(node);
            long[] longs = new long[size / 8];
            toLongs(node, longs, 0, 200);
            KeyNode parsed = parse(Bytes.longsToBytesLE(longs), 0, 200).node;
            Assert.assertEquals(time, Klong.getTime(parsed.getKlong(0)));
            for (int bit = 56; bit <= 61; bit++) {
                byte[] buffer = Bytes.longsToBytesLE(longs);
                buffer[32 + bit / 8] ^= (byte) (1 << (bit % 8));    // klong 0's bit 'bit'
                String refused = StoredValueNode.parseWithRightChecksum(buffer, size);
                Assert.assertTrue(time + ", bit " + bit + ": " + refused,
                        refused.startsWith("Bad time klong"));
            }
        }
    }
}
