package bergdb.core;

import bergdb.common.Bug;
import bergdb.common.Bytes;
import bergdb.dag.Node;
import bergdb.dag.Keys;
import bergdb.dag.Spos;
import bergdb.dag.ValueNode;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.storage.StreamFormatException;

/**
 * This class is responsible for how to store a ValueNode in the stream.
 * 
 * @author Frans Lundberg
 */
public class StoredValueNode implements StoredNode {
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
     */
    public static StoredValueNode parse(byte[] buffer, int offset, long spos) {
        assert buffer != null;
        assert buffer.length > offset;
        
        offset += 4; // Skips byte size.
        byte type = buffer[offset];
        offset += 1;
        if (type != Node.TYPE_VALUE && type != Node.TYPE_DELETE) {
            throw new Bug("Bad node type byte, " + ((int) type)
                    + ", should have been checked already.");
        }
        
        byte version = buffer[offset];
        offset += 1;
        
        if (version != 2) {
            throw new StreamFormatException("Cannot parse value node of "
                    + "format version " + version + ".");
        }
        
        offset += 2; // two bytes not used
        
        byte[] value = null;
        
        if (type == Node.TYPE_VALUE) {
            int valueSize = Bytes.bytesToIntLE(buffer, offset);
            offset += 4;
            value = new byte[valueSize];
            System.arraycopy(buffer, offset, value, 0, valueSize);
            offset += valueSize;
        }
        
        long[] key = new long[0];
        
        int keySize = Bytes.bytesToIntLE(buffer, offset);
        offset += 4;
        
        if (keySize % 8 != 0 || keySize <= 0) {
            throw new StreamFormatException("Bad key size when reading value node at spos " 
                    + spos + ", keySize: " + keySize + ".");
        }
        
        key = new long[keySize / 8];
        for (int i = 0; i < key.length; i++) {
            key[i] = Bytes.bytesToLongLE(buffer, offset);
            offset += 8;
        }
        
        ValueNode valueNode = new ValueNode(value, spos);
        StoredValueNode stored = new StoredValueNode();
        stored.node = valueNode;
        stored.key = key;

        return stored;
    }

    public static int getByteSize(ValueNode node, long[] key) {
        return node.value == null ? 
                8 +                         4 + 8 * key.length
              : 8 + 4 + node.value.length + 4 + 8 * key.length;
    }

    /**
     * The value is serialized to the byte buffer.
     * 
     * @return The number of bytes required to store the value node.
     */
    public static int toBytes(ValueNode node, long[] key, byte[] buffer, final int firstOffset) {
        int offset = firstOffset;
        int byteSize = getByteSize(node, key);
        long myLong;
        final long FORMAT_VERSION = 2L;    // serial format version (one byte)
        long nodeType = node.value == null ? Node.TYPE_DELETE : Node.TYPE_VALUE;

        myLong = ((long) byteSize) 
                | (nodeType << (4 * 8)) 
                | (FORMAT_VERSION << (5 * 8));
        
        Bytes.longToBytesLE(myLong, buffer, offset);
        offset += 8;
        // Room for 2 checksum bytes.

        if (nodeType == Node.TYPE_VALUE) {
            // DELETE nodes have no value.
            
            Bytes.intToBytesLE(node.value.length, buffer, offset);
            offset += 4;
            System.arraycopy(node.value, 0, buffer, offset, node.value.length);
            offset += node.value.length;    
        }
        
        Bytes.intToBytesLE(key.length * 8, buffer, offset);
        offset += 4;
        Bytes.longsToBytesLE(key, 0, key.length, buffer, offset);
        offset += 8 * key.length;
        

        // Checksum, XOR of all bytes to buffer[firstOffset + 6], 0 -> 1. 
        // 0 used as no checksum indicator.

        int checksum = 0;
        for (int i = 0; i < byteSize; i++) {
            checksum ^= buffer[firstOffset + i];
        }
        checksum = checksum & 0x000000ff;
        checksum = checksum == 0 ? 1 : checksum;
        buffer[firstOffset + 6] = (byte) checksum;

        assert offset - firstOffset == byteSize 
                : "offset:" + offset + ", firstOffset:" + firstOffset + ", byteSize: " + byteSize;
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

        StoredValueNode stored = parse(buffer, 0, 100);
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
        
        StoredValueNode stored = parse(buffer, 0, 100);
        
        Assert.assertArrayEquals(Keys.toSegments(keyString), stored.getKey());
    }
    
    @Nano
    private static void testThatSposIsSetWhenParsedFromBytes() {
        long[] key = Keys.toSegments("/-mykey.txt");
        ValueNode node = new ValueNode(new byte[0], Spos.NULL);
        byte[] buffer = new byte[getByteSize(node, key)];
        StoredValueNode.toBytes(node, key, buffer, 0);

        long spos = 120;
        StoredValueNode stored = parse(buffer, 0, spos);
        ValueNode node2 = stored.getNode();
        
        Assert.assertEquals(spos, node2.getSpos());
    }
    
    public static void main(String[] args) {
        testToBytesAndBack();
    }
}
