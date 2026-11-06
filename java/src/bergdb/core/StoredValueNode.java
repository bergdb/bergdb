package bergdb.core;

import bergdb.common.Bug;
import bergdb.common.Bytes;
import bergdb.dag.Node;
import bergdb.dag.Keys;
import bergdb.dag.Klong;
import bergdb.dag.Spos;
import bergdb.dag.ValueNode;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.storage.RecoverableStream;
import bergdb.storage.StreamFormatException;
import bergdb.storage.VersioningStreamException;

/**
 * This class is responsible for how to store a ValueNode in the stream.
 * 
 * @author Frans Lundberg
 */
public class StoredValueNode implements StoredNode {
    //
    // 160330, added offsetFromTrans.
    // 151114, from today size of StoredValueNode % 4 == 0.
    // We need alignment to allow for spos to determine node type.
    //
    
    public static final int ID_OFFSET = 8;
    
    /**
     * The smallest size of a stored value node: the header, 8 bytes; the id, 8; the offset
     * from the transaction, 4; and the value's or the key's size, 4.
     */
    static final int MIN_SIZE = 24;
    
    private ValueNode node;
    private long[] key;

    private StoredValueNode() {
    }

    public final ValueNode getNode() {
        return node;
    }
    
    public final ValueNode getValueNode() {
        return node;
    }
    
    public long getPrevPos() {
        return Spos.NULL;
    }
    
    public long[] getKey() {
        return key;
    }
    
    public String toString() {
        return "p:" + getPrevPos() + ", n:" + node.toString();
    }
    
    /**
     * Creates instance given a ValueNode and its key.
     * Useful for testing.
     */
    public static StoredValueNode create(ValueNode node, long[] key) {
        StoredValueNode result = new StoredValueNode();
        result.node = node;
        result.key = key;
        return result;
    }

    /**
     * Creates a StoredValueNode by parsing the provided byte buffer.
     * 
     * @throws StreamFormatException
     *      If a size of the node, of its value or of its key does not fit the node (2026-11-03,
     *      bergdb 015-07), or another field is wrong.
     */
    public static StoredValueNode parse(byte[] buffer, int offset, long spos) {
        assert buffer != null;
        assert buffer.length > offset;
        
        // The sizes are checked against the node's (2026-11-03, bergdb 015-07): a node whose
        // checksum was right but whose value or key size did not fit it threw a
        // NegativeArraySizeException or an ArrayIndexOutOfBoundsException, which escaped the
        // reads' failure handling, or read the bytes after it. 'end' is the node's end.
        final int nodeSize = Bytes.bytesToIntLE(buffer, offset);
        if (nodeSize < MIN_SIZE || nodeSize > buffer.length - offset) {
            throw new StreamFormatException("Bad value node size, " + nodeSize + ", at spos "
                    + spos + ".");
        }
        final int end = offset + nodeSize;
        
        offset += 4; // Skips byte size.
        byte type = buffer[offset];
        offset += 1;
        if (type != Node.TYPE_VALUE && type != Node.TYPE_DELETE) {
            throw new Bug("Bad node type byte, " + ((int) type)
                    + ", should have been checked already.");
        }
        
        byte version = buffer[offset];
        offset += 1;
        
        if (version != 4) {
            throw new VersioningStreamException("Cannot parse value node of "
                    + "format version " + version + ".");
        }
        
        offset += 2; // checksum bytes, checked before parsing
        
        long id = Bytes.bytesToLongLE(buffer, offset);
        offset += 8;
        
        int offsetFromTrans = Bytes.bytesToIntLE(buffer, offset);
        offset += 4;
        
        byte[] value = null;
        
        if (type == Node.TYPE_VALUE) {
            int valueSize = Bytes.bytesToIntLE(buffer, offset);
            offset += 4;
            if (valueSize < 0 || valueSize > end - offset - 4) {      // and the key's size
                throw new StreamFormatException("Bad value size, " + valueSize
                        + ", of value node at spos " + spos + ", size " + nodeSize + ".");
            }
            value = new byte[valueSize];
            System.arraycopy(buffer, offset, value, 0, valueSize);
            offset += valueSize;
        }
        
        long[] key = new long[0];
        
        int keySize = Bytes.bytesToIntLE(buffer, offset);
        offset += 4;
        
        if (keySize % 8 != 0 || keySize <= 0 || keySize > end - offset) {
            throw new StreamFormatException("Bad key size when reading value node at spos " 
                    + spos + ", keySize: " + keySize + ", node size: " + nodeSize + ".");
        }
        
        key = new long[keySize / 8];
        for (int i = 0; i < key.length; i++) {
            key[i] = Bytes.bytesToLongLE(buffer, offset);
            offset += 8;
        }
        if (!isKey(key)) {
            throw new StreamFormatException("Bad key of value node at spos " + spos + ".");
        }
        
        // The stored offset is in the record's bytes; the node keeps the distance in the
        // stream, which is longer by the meta blocks in between (2026-10-24, bergdb 005-34).
        long tpos;
        try {
            tpos = RecoverableStream.getStartSpos(spos, offsetFromTrans);
        } catch (IllegalArgumentException e) {
            throw new StreamFormatException("Bad offset from transaction, " + offsetFromTrans
                    + ", of value node at spos " + spos + ".");
        }
        
        ValueNode valueNode = new ValueNode(value, spos);
        valueNode.setId(id);
        valueNode.offsetFromTrans = (int) (spos - tpos);
        StoredValueNode stored = new StoredValueNode();
        stored.node = valueNode;
        stored.key = key;
        return stored;
    }

    /**
     * True if 'segments' is a key as Keys.toSegments makes it (2026-11-06, bergdb 019-32):
     * each segment a compare value (Klong.getCompareValue: bits 0 to 2, 62 and 63 zero), all
     * but the last of length 7, the last shorter. A start reruns a value node's key into the
     * graph (Dag.putKv), whose segments it takes for this; a key with a type bit set was taken,
     * and the rerun met an assert of the Core (Dag.setValue).
     */
    static boolean isKey(long[] segments) {
        for (int i = 0; i < segments.length; i++) {
            long s = segments[i];
            if ((s & 0xc000000000000007L) != 0
                    || (Klong.getLength(s) == Klong.MAX_SIZE) != (i < segments.length - 1)) {
                return false;
            }
        }
        return true;
    }

    public static int getByteSize(ValueNode node, long[] key) {
        int size = node.value == null ? 
                8 + 8 + 4 +                         4 + 8 * key.length
              : 8 + 8 + 4 + 4 + node.value.length + 4 + 8 * key.length;
        return size + Spos.addToAlign(size, 4);
    }
    
    /**
     * As getByteSize(), for a value (null for a delete) and a key, computed in long
     * (2026-10-21, bergdb 005-17): the int sum wraps for a value of close to 2^31 bytes.
     */
    public static long getByteSizeLong(byte[] value, long[] key) {
        long size = value == null ?
                8 + 8 + 4 +                                4 + 8L * key.length
              : 8 + 8 + 4 + 4 + (long) value.length + 4 + 8L * key.length;
        return size + (4 - size % 4) % 4;
    }

    /**
     * The value is serialized to the byte buffer. Not node.offsetFromTrans: the serializer
     * sets it before the node's spos (bergdb 005-34).
     * 
     * @param bufferOffset
     *      Offset in buffer to start writing to. Also, offset from start of transaction in
     *      the record's bytes, as it is stored; the distance in the stream is longer by the
     *      meta blocks in between (bergdb 005-34).
     * @return 
     *      The number of bytes required to store the value node.
     */
    public static int toBytes(ValueNode node, long[] key, byte[] buffer, final int bufferOffset) {
        int offset = bufferOffset;
        int byteSize = getByteSize(node, key);
        long myLong;
        final long FORMAT_VERSION = 4L;     // serial format version (one byte)
        long nodeType = node.value == null ? Node.TYPE_DELETE : Node.TYPE_VALUE;

        myLong = ((long) byteSize) 
                | (nodeType << (4 * 8)) 
                | (FORMAT_VERSION << (5 * 8));
        
        Bytes.longToBytesLE(myLong, buffer, offset);
        offset += 8;
        // Room for 2 checksum bytes.
        
        Bytes.longToBytesLE(node.getId(), buffer, offset);
        offset += 8;
        
        int offsetFromTrans = bufferOffset;
        Bytes.intToBytesLE(offsetFromTrans, buffer, offset);
        offset += 4;

        if (nodeType == Node.TYPE_VALUE) {
            // only TYPE_VALUE (not TYPE_DELETE) have value
            
            Bytes.intToBytesLE(node.value.length, buffer, offset);
            offset += 4;
            System.arraycopy(node.value, 0, buffer, offset, node.value.length);
            offset += node.value.length;    
        }
        
        Bytes.intToBytesLE(key.length * 8, buffer, offset);
        offset += 4;
        Bytes.longsToBytesLE(key, 0, key.length, buffer, offset);
        offset += 8 * key.length;
        
        // Zeros the alignment padding: the buffer may hold earlier bytes, and the
        // padding is part of the checksum.
        for (int i = offset; i < bufferOffset + byteSize; i++) {
            buffer[i] = 0;
        }

        int checksum = NodeChecksum.sum(buffer, bufferOffset, byteSize);
        Bytes.ushortToBytesLE(checksum, buffer, bufferOffset + 6);

        int sizeHere = offset - bufferOffset;
        assert sizeHere + Spos.addToAlign(sizeHere, 4) == byteSize
                : "offset:" + offset + ", firstOffset:" + bufferOffset + ", byteSize: " + byteSize;
        
        return byteSize;
    }

    
    // ======== Tests ========

    @Nano
    private static void testToBytesAndBack() {
        byte[] value = new byte[10];
        value[3] = 3;
        value[9] = -2;
        long[] key = Keys.toSegments("/-mykey.txt");

        ValueNode node = new ValueNode(value, Spos.NULL);
        byte[] buffer = new byte[getByteSize(node, key)];
        StoredValueNode.toBytes(node, key, buffer, 0);

        StoredValueNode stored = parse(buffer, 0, 128);
        ValueNode node2 = stored.getNode();
        
        Assert.assertEquals(getByteSize(node, key), getByteSize(node2, key));
        Assert.assertArrayEquals(node.value, node2.value);
    }
    
    @Nano
    private static void testToBytesAndBackAndCheckKey() {
        final String keyString = "a";
        long[] key = Keys.toSegments(keyString);
        ValueNode node = new ValueNode(new byte[0], Spos.NULL);
        byte[] buffer = new byte[getByteSize(node, key)];
        
        StoredValueNode.toBytes(node, key, buffer, 0);
        
        StoredValueNode stored = parse(buffer, 0, 128);
        
        Assert.assertArrayEquals(Keys.toSegments(keyString), stored.getKey());
    }
    
    /** A value node of another format version is refused as one (2026-10-25, bergdb 005-40). */
    @Nano
    private static void testRefusesOtherVersion() {
        long[] key = Keys.toSegments("a");
        ValueNode node = new ValueNode(new byte[3], Spos.NULL);
        byte[] buffer = new byte[getByteSize(node, key)];
        StoredValueNode.toBytes(node, key, buffer, 0);
        Assert.assertEquals(4, buffer[5]);
        buffer[5] = 5;
        
        try {
            parse(buffer, 0, 128);
            throw new AssertionError("parsed");
        } catch (VersioningStreamException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("format version 5"));
        }
    }
    
    @Nano
    private static void testThatSposIsSetWhenParsedFromBytes() {
        long[] key = Keys.toSegments("/-mykey.txt");
        ValueNode node = new ValueNode(new byte[0], Spos.NULL);
        byte[] buffer = new byte[getByteSize(node, key)];
        StoredValueNode.toBytes(node, key, buffer, 0);

        long spos = 136;
        StoredValueNode stored = parse(buffer, 0, spos);
        ValueNode node2 = stored.getNode();
        
        Assert.assertEquals(spos, node2.getSpos());
    }
    
    @Nano
    private static void testOffsetFromTrans() {
        byte[] value = new byte[10];
        long[] key = Keys.toSegments("/-mykey.txt");

        ValueNode node = new ValueNode(value, Spos.NULL);
        byte[] buffer = new byte[120 + getByteSize(node, key)];
        StoredValueNode.toBytes(node, key, buffer, 120);

        StoredValueNode stored = parse(buffer, 120, 128 + 120);
        Assert.assertEquals(120L, stored.getNode().getOffsetFromTrans());
        Assert.assertEquals(128L, stored.getNode().getTpos());
    }
    
    /**
     * Regression test for bergdb 005-34: for a value node after a meta block in its record,
     * the stored offset (in the record's bytes) is 128 bytes shorter than the distance in the
     * stream, and the transaction's position was 128 bytes too far.
     */
    @Nano
    private static void testOffsetFromTransAcrossMetaBlock() {
        final int d = RecoverableStream.META_BLOCK_DISTANCE;
        final int m = RecoverableStream.META_BLOCK_SIZE;
        long[] key = Keys.toSegments("/-mykey.txt");
        ValueNode node = new ValueNode(new byte[10], Spos.NULL);
        byte[] buffer = new byte[5000 + getByteSize(node, key)];
        StoredValueNode.toBytes(node, key, buffer, 5000);
        
        long tpos = d - 2000;                       // The record crosses the meta block at d.
        long spos = RecoverableStream.getSpos(tpos, 5000);
        Assert.assertEquals(tpos + 5000 + m, spos);
        ValueNode parsed = parse(buffer, 5000, spos).getNode();
        Assert.assertEquals(5000L + m, parsed.getOffsetFromTrans());
        Assert.assertEquals(tpos, parsed.getTpos());
        
        long far = 7L * d + 1000;                   // At 2^31 and beyond: an unsigned int.
        long farSpos = RecoverableStream.getSpos(far, Integer.MAX_VALUE - 101);  // Even.
        ValueNode n = new ValueNode(new byte[0]);
        n.offsetFromTrans = (int) (farSpos - far);
        n.setSpos(farSpos);
        Assert.assertTrue(farSpos - far > Integer.MAX_VALUE);
        Assert.assertEquals(far, n.getTpos());
        
        n.setSpos(farSpos + 1);                     // A vpos: not written yet.
        Assert.assertEquals(Spos.NULL, n.getTpos());
        n.setSpos(Spos.NULL);
        Assert.assertEquals(Spos.NULL, n.getTpos());
        
        try {
            parse(buffer, 5000, m + 1000);          // Starts before the stream's first byte.
            throw new AssertionError("parsed");
        } catch (StreamFormatException e) {
            // Expected.
        }
    }
    
    /**
     * A value node whose checksum is right but whose sizes do not fit it is refused with a
     * StreamFormatException, by NodeStream.bytesToNode as a load and a record's parse call it
     * (2026-11-03, bergdb 015-07). Before: a value size of -1 threw a
     * NegativeArraySizeException; one of 1,000, and a key size of 8,000, an
     * ArrayIndexOutOfBoundsException; a key size 16 bytes past the node, and a node size of
     * 20, read the bytes after the node, which the buffer holds here as in a load.
     */
    @Nano
    private static void testRefusesSizesBeyondTheNode() {
        long[] key = Keys.toSegments("/-mykey.txt");
        ValueNode node = new ValueNode(new byte[10], Spos.NULL);
        final int size = getByteSize(node, key);
        final int valueAt = 20, keyAt = 24 + 10;
        // The field's offset, its value, and what the message starts with.
        Object[][] cases = {
            {valueAt, -1, "Bad value size"},
            {valueAt, 1000, "Bad value size"},
            {keyAt, 8000, "Bad key size"},
            {keyAt, 8 * key.length + 16, "Bad key size"},
            {0, 20, "Bad value node size"},
        };
        for (Object[] c : cases) {
            byte[] buffer = new byte[size + 64];
            toBytes(node, key, buffer, 0);
            Bytes.intToBytesLE((Integer) c[1], buffer, (Integer) c[0]);
            final int n = (Integer) c[0] == 0 ? (Integer) c[1] : size;
            String refused = parseWithRightChecksum(buffer, n);
            Assert.assertTrue("at " + c[0] + ", " + c[1] + ": " + refused,
                    refused.startsWith((String) c[2]));
        }
    }
    
    /**
     * A value node whose checksum is right but whose key is not one that Keys.toSegments
     * makes is refused with a StreamFormatException (2026-11-06, bergdb 019-32): a segment
     * with bit 63 (a klong's type) or bit 0 set, a last segment of length 7, and a segment
     * of length 6 before the last. Before, each was parsed, and a start's rerun of the
     * value's key met an assert of the Core (harness 6.1, bergdb 018-07: a key's byte 7 xor
     * 0x80).
     */
    @Nano
    private static void testRefusesBadKey() {
        long[] key = Keys.toSegments("/-mykey.txt");      // two segments, of 7 and 4 bytes
        Assert.assertEquals(2, key.length);
        ValueNode node = new ValueNode(new byte[10], Spos.NULL);
        final int size = getByteSize(node, key);
        final int keyAt = 24 + 10 + 4;
        long[][] bad = {
            {key[0], key[1] ^ (1L << 63)},
            {key[0], key[1] | 1},
            {key[0], key[1] | (7 << 3)},
            {key[0] & ~(1L << 3), key[1]},
        };
        for (long[] b : bad) {
            byte[] buffer = new byte[size];
            toBytes(node, key, buffer, 0);
            Bytes.longToBytesLE(b[0], buffer, keyAt);
            Bytes.longToBytesLE(b[1], buffer, keyAt + 8);
            String refused = parseWithRightChecksum(buffer, size);
            Assert.assertTrue(Long.toHexString(b[0]) + " " + Long.toHexString(b[1]) + ": "
                    + refused, refused.startsWith("Bad key of value node"));
        }
        byte[] buffer = new byte[size];
        toBytes(node, key, buffer, 0);
        Bytes.ushortToBytesLE(NodeChecksum.sumWithZeroReplace(buffer, 0, size, 6), buffer, 6);
        NodeStream.bytesToNode(128, buffer, 0, size);       // The key as it is: taken.
    }
    
    /**
     * Gives the node at the start of 'buffer', its size 'size', its checksum, and parses it as
     * NodeStream.bytesToNode does (bergdb 015-07's tests); returns the StreamFormatException's
     * message. It must not be a checksum's.
     */
    static String parseWithRightChecksum(byte[] buffer, int size) {
        Bytes.ushortToBytesLE(NodeChecksum.sumWithZeroReplace(buffer, 0, size, 6), buffer, 6);
        try {
            NodeStream.bytesToNode(128, buffer, 0, size);
        } catch (StreamChecksumException e) {
            throw new AssertionError("a checksum error", e);
        } catch (StreamFormatException e) {
            return e.getMessage();
        }
        throw new AssertionError("parsed");
    }
}
