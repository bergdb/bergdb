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
        final long FORMAT_VERSION = 2;     // serial format version (one byte)

        buffer[offset++] = 
                  ((long) byteSize) 
                | (((long) Node.TYPE_KEY_NODE) << (4 * 8))
                | (FORMAT_VERSION << (5 * 8));
        
        // 2 bytes available for checksum
        
        buffer[offset++] = prevPos;
        buffer[offset++] = ((long) (node.isSegmentLeaf() ? 1 : 0)) | sz << (1 * 8);
        // 5 zero bytes available...
        buffer[offset++] = node.getId();

        System.arraycopy(node.klongs, 0, buffer, offset, sz);
        offset += sz;
        
        for (int i = 0; i < sz; i++) {
            buffer[offset++] = node.getSerializedRef(i);
        }
        
        long checksum = NodeChecksum.sum(buffer, firstOffset, offset - firstOffset);
        buffer[firstOffset] = buffer[firstOffset] | (checksum << (6 * 8));

        assert (offset - firstOffset) * 8 == byteSize;
        assert byteSize % 8 == 0;
        return byteSize / 8;
    }

    /**
     * @throws StreamFormatException
     */
    public static StoredKeyNode parse(byte[] buffer, int offset, long spos) {
        offset += 4; // Skip size.
        byte type = buffer[offset];
        offset += 1;
        if (type != Node.TYPE_KEY_NODE) {
            throw new Bug("Bad node type byte, " + ((int) type)
                    + ", should have been checked already.");
        }

        byte version = buffer[offset];
        
        if (version != 2) {
            throw new VersioningStreamException("Cannot parse key node of format version "
                    + version + ".");
        }
        
        offset += 1;

        offset += 2; // checksum bytes
        
        // offset == 8 here

        long prevPos = Bytes.bytesToLongLE(buffer, offset);
        if (!Spos.isValidOrNull(prevPos)) {
            throw new StreamFormatException("Bad KeyNode, prevPos is illegal: " + prevPos + ".");
        }
        offset += 8;

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

        // 5 zero bytes
        offset += 5;
        
        // offset == 24 here

        long id = Bytes.bytesToLongLE(buffer, offset);
        offset += 8;

        if (size < 0) {
            throw new StreamFormatException("Bad Node size, " + size + ".");
        }

        long[] klongs = new long[size];
        long[] positions = new long[size];

        for (int i = 0; i < size; i++) {
            klongs[i] = Bytes.bytesToLongLE(buffer, offset);
            offset += 8;
        }

        for (int i = 0; i < size; i++) {
            positions[i] = Bytes.bytesToLongLE(buffer, offset);
            offset += 8;
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
        Assert.assertEquals(2, byteBuffer[5]);
        byteBuffer[5] = 3;
        
        try {
            StoredKeyNode.parse(byteBuffer, 0, 0);
            throw new AssertionError("parsed");
        } catch (VersioningStreamException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("format version 3"));
        }
    }
}
