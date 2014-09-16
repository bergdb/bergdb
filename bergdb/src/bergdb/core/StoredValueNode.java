package bergdb.core;

import bergdb.common.Bug;
import bergdb.common.Bytes;
import bergdb.common.Pair;
import bergdb.dag.INode;
import bergdb.dag.Keys;
import bergdb.dag.Spos;
import bergdb.dag.ValueNode;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
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
    
    public long getPrevPos() {
        return Spos.NULL;
    }
    
    public long[] getKey() {
        return key;
    }

    /**
     * Creates a StoredValueNode by parsing the provided byte buffer.
     */
    public static StoredValueNode parse(byte[] buffer, int offset, long spos, boolean readKey) {
        Pair<ValueNode, long[]> pair = fromBytes(buffer, offset, spos, readKey);

        StoredValueNode stored = new StoredValueNode();
        stored.node = pair.getValue0();
        stored.key = pair.getValue1();

        return stored;
    }

    /**
     * @throws StreamFormatException
     */
    private static Pair<ValueNode, long[]> fromBytes(byte[] buffer, int offset, long spos, boolean readKey) {
        assert buffer != null;
        assert buffer.length > offset;

        offset += 4; // Skips byte size.
        byte type = buffer[offset];
        offset += 1;
        if (type != INode.TYPE_VALUE && type != INode.TYPE_DELETE) {
            throw new Bug("Bad node type byte, " + ((int) type)
                    + ", should have been checked already.");
        }

        Pair<ValueNode, long[]> result;

        if (type == INode.TYPE_DELETE) {
            byte version = buffer[offset];
            offset += 1;

            if (version != 1) {
                throw new StreamFormatException("Can only handle ValueNode of "
                        + "version 1, got version " + version + ".");
            }

            ValueNode valueNode = new ValueNode(null);
            valueNode.spos = spos;
            result = new Pair<ValueNode, long[]>(valueNode, new long[0]);
        } else {
            byte version = buffer[offset];
            offset += 1;

            if (version != 1) {
                throw new StreamFormatException("Can only handle ValueNode of "
                        + "version 1, got version " + version + ".");
            }

            offset += 2; // two bytes not used

            int size = Bytes.bytesToIntLE(buffer, offset);
            offset += 4;

            byte[] value = new byte[size];
            System.arraycopy(buffer, offset, value, 0, size);
            offset += size;
            
            long[] key = new long[0];
            
            if (readKey) {
                int keySize = Bytes.bytesToIntLE(buffer, offset);
                if (keySize % 8 != 0 || keySize <= 0) {
                    throw new StreamFormatException("Bad key size when reading value node at spos " 
                            + spos + ", keySize: " + keySize + ".");
                }
                
                key = new long[keySize / 8];
                for (int i = 0; i < key.length; i++) {
                    key[i] = Bytes.bytesToLongLE(buffer, offset);
                    offset += 8;
                }
            }
            
            ValueNode valueNode = new ValueNode(value);
            result = new Pair<ValueNode, long[]>(valueNode, key);
        }

        return result;
    }

    public static int getByteSize(ValueNode node, long[] key) {
        return node.value == null ? 
                8 : 
                8 + 4 + node.value.length + 4 + 8* key.length;
    }

    /**
     * The value is serialized to the byte buffer.
     */
    public static int toBytes(ValueNode node, long[] key, byte[] buffer, final int firstOffset) {
        int offset = firstOffset;
        int byteSize = getByteSize(node, key);
        long myLong;
        long nodeType = node.value == null ? INode.TYPE_DELETE : INode.TYPE_VALUE;

        myLong = ((long) byteSize) | (nodeType << (4 * 8)) | (1L << (5 * 8));
        Bytes.longToBytesLE(myLong, buffer, offset);
        offset += 8;
        // Room for 2 checksum bytes.

        if (nodeType == INode.TYPE_VALUE) {
            Bytes.intToBytesLE(node.value.length, buffer, offset);
            offset += 4;

            System.arraycopy(node.value, 0, buffer, offset, node.value.length);
            offset += node.value.length;
            
            Bytes.intToBytesLE(key.length * 8, buffer, offset);
            offset += 4;
            
            Bytes.longsToBytesLE(key, 0, key.length, buffer, offset);
            offset += 8 * key.length;
            
            
        } else {
            // For a TYPE_DELETE, we have no value, no key.
        }

        // Checksum, XOR of all bytes to buffer[firstOffset + 6], 0 -> 1. 0 used as no checksum
        // indicator.

        int checksum = 0;
        for (int i = 0; i < byteSize; i++) {
            checksum ^= buffer[firstOffset + i];
        }
        checksum = checksum & 0x000000ff;
        checksum = checksum == 0 ? 1 : checksum;
        buffer[firstOffset + 6] = (byte) checksum;

        assert offset - firstOffset == byteSize;
        return byteSize;
    }

    
    // ======== Tests ========

    @T
    public static void testToBytesAndBack() {
        byte[] value = new byte[10];
        value[3] = 3;
        value[9] = -2;
        long[] key = Keys.toSegments("/-mykey.txt");

        ValueNode node = new ValueNode(value);
        byte[] buffer = new byte[getByteSize(node, key)];
        StoredValueNode.toBytes(node, key, buffer, 0);

        StoredValueNode stored = parse(buffer, 0, Spos.NULL, true);
        ValueNode node2 = stored.getNode();
        
        Assert.assertEquals(getByteSize(node, key), getByteSize(node2, key));
        Assert.assertArrayEquals(node.value, node2.value);
    }
    
    public static void main(String[] args) {
        testToBytesAndBack();
    }
}
