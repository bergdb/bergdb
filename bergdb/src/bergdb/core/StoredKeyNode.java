package bergdb.core;

import bergdb.common.Bug;
import bergdb.common.Bytes;
import bergdb.dag.INode;
import bergdb.dag.KeyNode;
import bergdb.dag.Spos;
import bergdb.storage.StreamFormatException;

/**
 * This class is responsible for how to store a KeyNode in the stream.
 * Serialization/deserialization and the extra prevPos field that is 
 * only available in the stored node.
 * 
 * @author Frans Lundberg
 */
public class StoredKeyNode {
    private KeyNode node;
    private long prevPos;
    
    private StoredKeyNode() {}
    
    public KeyNode getNode() {
        return node;
    }
    
    public long getPrevPos() {
        return prevPos;
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
        
        buffer[offset++] = ((long)byteSize) | (((long)INode.TYPE_KEY_NODE) << (4*8)) | (1L << (5*8));
            // 2 bytes available for checksum
        buffer[offset++] = prevPos;
        buffer[offset++] = ((long) (node.isSegmentLeaf() ? 1 : 0)) | sz << (1*8);
            // 5 zero bytes available...
        buffer[offset++] = node.getId();
        
        System.arraycopy(node.klongs, 0, buffer, offset, sz);
        offset += sz;
        
        for (int i = 0; i < sz; i++) {
            long spos = node.pointers[i] == null ? node.pos[i] : node.pointers[i].getSpos();
            buffer[offset++] = spos;
        }
        
        // Checksum, XOR of all bytes.
        
        long checksum = 0;
        for (int i = firstOffset; i < offset; i++) {
            checksum ^= buffer[i];
        }
        
        checksum = 0x000000ff &
               ((checksum >>> 0)  ^ (checksum >>> 8)  ^ (checksum >>> 16) ^ (checksum >>> 24)
              ^ (checksum >>> 32) ^ (checksum >>> 40) ^ (checksum >>> 48) ^ (checksum >>> 56));
        checksum = checksum == 0 ? 1 : checksum;
        buffer[firstOffset] = buffer[firstOffset] | (checksum << (6*8));
        
        assert (offset - firstOffset) * 8 == byteSize;
        assert byteSize % 8 == 0;
        return byteSize / 8;
    }
    
    /**
     * @throws StreamFormatException
     */
    public static StoredKeyNode createFromBytes(byte[] buffer, int offset, long spos) {
        offset += 4;          // Skip size.
        byte type = buffer[offset];
        offset += 1;
        if (type != INode.TYPE_KEY_NODE) {
            throw new Bug("Bad node type byte, " + ((int) type) 
                    + ", should have been checked already.");
        }
        
        byte version = buffer[offset];
        if (version != 1) {
            throw new StreamFormatException("Bad Node stream format version, expected 1, was " 
                    + ((int)version) + ".");
        }
        offset += 1;
        
        offset += 2;    // checksum bytes
        
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
        
        keyNode.size = keyNode.size;     // Synch action to publish writes.
        
        StoredKeyNode result = new StoredKeyNode();
        result.node = keyNode;
        result.prevPos = prevPos;
        return result;
    } 
    
    // TODO C. Test serialization.
    
}
