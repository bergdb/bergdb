package bergdb.core;

import bergdb.common.Bug;
import bergdb.common.Bytes;
import bergdb.common.Pair;
import bergdb.dag.Choices;
import bergdb.dag.INode;
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
    private byte[] choices;

    private StoredValueNode() {
    }

    public final ValueNode getNode() {
        return node;
    }

    public final byte[] getChoices() {
        return choices;
    }
    
    public long getPrevPos() {
        return Spos.NULL;
    }

    /**
     * Creates a StoredValueNode by parsing the provided byte buffer.
     */
    public static StoredValueNode parse(byte[] buffer, int offset, long spos) {
        Pair<ValueNode, byte[]> pair = fromBytesIncludingChoices(buffer, offset, spos);

        StoredValueNode stored = new StoredValueNode();
        stored.node = pair.getValue0();
        stored.choices = pair.getValue1();

        return stored;
    }

    /**
     * @throws StreamFormatException
     */
    private static Pair<ValueNode, byte[]> fromBytesIncludingChoices(byte[] buffer, int offset,
            long spos) {
        assert buffer != null;
        assert buffer.length > offset;

        offset += 4; // Skips byte size.
        byte type = buffer[offset];
        offset += 1;
        if (type != INode.TYPE_VALUE && type != INode.TYPE_DELETE) {
            throw new Bug("Bad node type byte, " + ((int) type)
                    + ", should have been checked already.");
        }

        Pair<ValueNode, byte[]> result;

        if (type == INode.TYPE_DELETE) {
            byte version = buffer[offset];
            offset += 1;

            if (version != 1) {
                throw new StreamFormatException("Can only handle ValueNode of "
                        + "version 1, got version " + version + ".");
            }

            short size = Bytes.bytesToShortLE(buffer, offset);
            offset += 2;
            byte[] choices = new byte[size];
            System.arraycopy(buffer, offset, choices, 0, size);
            offset += size;

            ValueNode valueNode = new ValueNode(null);
            valueNode.spos = spos;
            result = new Pair<ValueNode, byte[]>(valueNode, choices);
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

            size = Bytes.bytesToShortLE(buffer, offset);
            offset += 2;
            byte[] choices = new byte[size];
            try {
                System.arraycopy(buffer, offset, choices, 0, size);
            } catch (ArrayIndexOutOfBoundsException e) {
                throw new ArrayIndexOutOfBoundsException(e.getMessage() + "; size=" + size
                        + ", buffer.length=" + buffer.length + ", offset=" + offset);
            }
            offset += size;

            ValueNode valueNode = new ValueNode(value);
            valueNode.spos = spos;
            result = new Pair<ValueNode, byte[]>(valueNode, choices);
        }

        return result;
    }

    public static int getByteSize(ValueNode node, int choicesSize) {
        return node.value == null ? 8 + 2 + choicesSize : 8 + 4 + node.value.length + 2
                + choicesSize;
    }

    /**
     * The value is serialized to the byte buffer.
     */
    public static int toBytes(ValueNode node, Choices choices, byte[] buffer, final int firstOffset) {
        int offset = firstOffset;
        int byteSize = getByteSize(node, choices.size);
        long myLong;
        long nodeType = node.value == null ? INode.TYPE_DELETE : INode.TYPE_VALUE;

        if (choices.size > Short.MAX_VALUE) {
            throw new Bug("Bad size of choices, " + choices.size);
        }

        myLong = ((long) byteSize) | (nodeType << (4 * 8)) | (1L << (5 * 8));
        Bytes.longToBytesLE(myLong, buffer, offset);
        offset += 8;
        // Room for 2 checksum bytes.

        if (nodeType == INode.TYPE_VALUE) {
            Bytes.intToBytesLE(node.value.length, buffer, offset);
            offset += 4;

            System.arraycopy(node.value, 0, buffer, offset, node.value.length);
            offset += node.value.length;

            Bytes.shortToBytesLE((short) choices.size, buffer, offset);
            offset += 2;
            System.arraycopy(choices.choices, 0, buffer, offset, choices.size);
            offset += choices.size;
        } else {
            // For a TYPE_DELETE, only choices are written, we have no value.
            Bytes.shortToBytesLE((short) choices.size, buffer, offset);
            offset += 2;
            System.arraycopy(choices.choices, 0, buffer, offset, choices.size);
            offset += choices.size;
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
    public static void testToBytes() {
        byte[] value = new byte[10];
        value[3] = 3;
        value[9] = -2;

        ValueNode node = new ValueNode(value);
        byte[] buffer = new byte[getByteSize(node, 0)];
        toBytes(node, new Choices(), buffer, 0);

        ValueNode node2 = parse(buffer, 0, Spos.NULL).getNode();
        Assert.assertEquals(getByteSize(node, 0), getByteSize(node2, 0));
        Assert.assertArrayEquals(node.value, node2.value);
    }
}
