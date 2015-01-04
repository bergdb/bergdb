package bergdb.core;

// TODO LATER Refactor checksum computation. StoredKeyNode, StoredTopNode, StoredValueNode.
// TODO LATER Use checksum checking for StoredKeyNode, StoredTopNode, StoredValueNode.

import bergdb.common.AssertStatus;
import bergdb.common.Bug;
import bergdb.common.Bytes;
import bergdb.common.Util;
import bergdb.dag.INode;
import bergdb.dag.KeyNode;
import bergdb.dag.Klong;
import bergdb.dag.Spos;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.storage.StreamFormatException;

/**
 * This class is responsible for how to store a KeyNode in the stream. Serialization/deserialization
 * and the extra prevPos field that is only available in the stored node.
 * 
 * @author Frans Lundberg
 */
public class StoredKeyNode implements StoredNode {
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

        buffer[offset++] = 
                  ((long) byteSize) 
                | (((long) INode.TYPE_KEY_NODE) << (4 * 8))
                | (1L << (5 * 8));
        // 2 bytes available for checksum
        buffer[offset++] = prevPos;
        buffer[offset++] = ((long) (node.isSegmentLeaf() ? 1 : 0)) | sz << (1 * 8);
        // 5 zero bytes available...
        buffer[offset++] = node.getId();

        System.arraycopy(node.klongs, 0, buffer, offset, sz);
        offset += sz;

        for (int i = 0; i < sz; i++) {
            long spos = node.pointers[i] == null ? node.pos[i] : node.pointers[i].getSpos(); 
            
            // TODO B. Consider enabling this check.
            /*if (AssertStatus.enabled()) {
                long klong = node.getKlong(i);
                if (Klong.isKey(klong)) {
                    if (!Spos.isValid(spos)) {
                        throw new AssertionError("bad spos of pointer from KeyNode, spos:" 
                                + spos + ", i=" + i + ", node: " + node.print());
                    }
                }
            }*/
            
            buffer[offset++] = spos;
        }

        // Checksum, XOR of all bytes.

        long checksum = 0;
        for (int i = firstOffset; i < offset; i++) {
            checksum ^= buffer[i];
        }

        checksum = 0x000000ff & (
                  (checksum >>>  0) ^ (checksum >>>  8) ^ (checksum >>> 16) ^ (checksum >>> 24) ^ 
                  (checksum >>> 32) ^ (checksum >>> 40) ^ (checksum >>> 48) ^ (checksum >>> 56) );
        
        checksum = checksum == 0 ? 1 : checksum;
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
        if (type != INode.TYPE_KEY_NODE) {
            throw new Bug("Bad node type byte, " + ((int) type)
                    + ", should have been checked already.");
        }

        byte version = buffer[offset];
        if (version != 1) {
            throw new StreamFormatException("Bad Node stream format version, expected 1, was "
                    + ((int) version) + ".");
        }
        offset += 1;

        offset += 2; // checksum bytes

        long prevPos = Bytes.bytesToLongLE(buffer, offset);
        if (prevPos != Spos.NULL && prevPos < 0) {
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
        long k1 = Klong.create(Util.toBytes("key"));
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
}
