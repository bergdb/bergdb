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
    //
    // 160330, added offsetFromTrans.
    // 151114, from today size of StoredValueNode % 4 == 0.
    // We need alignment to allow for spos to determine node type.
    //
    
    public static final int ID_OFFSET = 8;
    
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
        
        if (version != 4) {
            throw new StreamFormatException("Cannot parse value node of "
                    + "format version " + version + ".");
        }
        
        offset += 2; // two bytes not used
        
        long id = Bytes.bytesToLongLE(buffer, offset);
        offset += 8;
        
        int offsetFromTrans = Bytes.bytesToIntLE(buffer, offset);
        offset += 4;
        
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
        valueNode.setId(id);
        StoredValueNode stored = new StoredValueNode();
        stored.node = valueNode;
        stored.key = key;
        valueNode.offsetFromTrans = offsetFromTrans;
        return stored;
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
     * The value is serialized to the byte buffer.
     * node.offsetFromTrans is set.
     * 
     * @param bufferOffset
     *      Offset in buffer to start writing to. Also, offset from start of transaction.
     *      Assumed to be the same (easy to change if/when needed).
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
        
        node.offsetFromTrans = offsetFromTrans;
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
    
    @Nano
    private static void testOffsetFromTrans() {
        byte[] value = new byte[10];
        long[] key = Keys.toSegments("/-mykey.txt");

        ValueNode node = new ValueNode(value, Spos.NULL);
        byte[] buffer = new byte[120 + getByteSize(node, key)];
        StoredValueNode.toBytes(node, key, buffer, 120);

        StoredValueNode stored = parse(buffer, 120, 222);
        Assert.assertEquals(120, stored.getNode().getOffsetFromTrans());
    }
}
