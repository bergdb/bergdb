package bergdb.core;

import java.util.zip.CRC32C;

import bergdb.common.Bytes;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * The checksum of a stored node, record format 7 (bergdb 024-25): CRC-32C, the Castagnoli
 * polynomial (java.util.zip.CRC32C, as iSCSI's, RFC 3720), of the node's bytes with its
 * checksum field left out: bytes 0 to 7, then bytes 12 to the node's end. It is stored
 * little-endian in bytes 8 to 11, the last four of the node's 12-byte header (bergdb
 * 024-02, section 9). The writer sets it when the node's other bytes are written
 * (StoredValueNode.toBytes; for top and key nodes StoredTrans.Serializer, after their
 * longs are copied to the record's bytes); a read checks it before it parses the node
 * (NodeStream.bytesToNode).
 *
 * <p>Until 024-25 the sum was Fletcher-16 modulo 255 in bytes 6 and 7: 16 bits, blind to a
 * byte changed between 0x00 and 0xff (bergdb 019-33), and 5.7 ms a MB against about 0.1
 * for CRC32C, which uses the CPU's instructions (bergdb 024-17, F6).</p>
 *
 * @author Frans Lundberg
 */
public final class NodeChecksum {
    /** The checksum's offset in a node. */
    public static final int OFFSET = 8;

    /** The checksum's size in bytes. */
    public static final int SIZE = 4;

    /** The node header's size: the size, the type, the format, two zero bytes, the sum. */
    public static final int HEADER_SIZE = OFFSET + SIZE;

    private NodeChecksum() {}

    /**
     * The checksum of the node of 'length' bytes at 'offset' in 'data', its bytes 8 to 11
     * left out. 'length' is at least HEADER_SIZE.
     */
    public static int sum(byte[] data, int offset, int length) {
        if (length < HEADER_SIZE) {
            throw new IllegalArgumentException("A node of " + length + " bytes.");
        }
        CRC32C crc = new CRC32C();
        crc.update(data, offset, OFFSET);
        crc.update(data, offset + HEADER_SIZE, length - HEADER_SIZE);
        return (int) crc.getValue();
    }

    /** Sets the checksum of the node of 'length' bytes at 'offset' in 'data'. */
    public static void set(byte[] data, int offset, int length) {
        Bytes.intToBytesLE(sum(data, offset, length), data, offset + OFFSET);
    }

    /** The checksum stored in the node at 'offset' in 'data'. */
    public static int stored(byte[] data, int offset) {
        return Bytes.bytesToIntLE(data, offset + OFFSET);
    }


    // ======== Testing ========

    /** CRC-32C's check value: of the ASCII bytes "123456789", 0xe3069283 (RFC 3720). */
    @Nano private static void testCheckValue() {
        final int length = HEADER_SIZE + 1;
        byte[] node = new byte[length + 1];
        byte[] digits = "123456789".getBytes(java.nio.charset.StandardCharsets.US_ASCII);
        System.arraycopy(digits, 0, node, 0, 8);
        System.arraycopy(digits, 8, node, HEADER_SIZE, 1);
        for (int i = OFFSET; i < HEADER_SIZE; i++) {
            node[i] = (byte) 0xa5;          // left out
        }
        node[length] = 0x77;                // after the node
        Assert.assertEquals(0xe3069283, sum(node, 0, length));
    }

    /** The sum leaves out bytes 8 to 11 and nothing else; set and stored agree. */
    @Nano private static void testField() {
        byte[] data = new byte[40];
        for (int i = 0; i < data.length; i++) {
            data[i] = (byte) (i * 37 + 1);
        }
        final int offset = 3;
        final int length = 32;
        int s = sum(data, offset, length);
        for (int i = offset + OFFSET; i < offset + HEADER_SIZE; i++) {
            data[i] ^= 0x5a;
            Assert.assertEquals(s, sum(data, offset, length));
        }
        set(data, offset, length);
        Assert.assertEquals(s, stored(data, offset));
        Assert.assertEquals(s, sum(data, offset, length));
        for (int i = offset; i < offset + length; i++) {
            if (i >= offset + OFFSET && i < offset + HEADER_SIZE) {
                continue;
            }
            for (int mask : new int[] {0x01, 0x80, 0xff}) {
                data[i] ^= (byte) mask;
                Assert.assertTrue(i + ", " + mask, sum(data, offset, length) != s);
                data[i] ^= (byte) mask;
            }
        }
        data[offset + length] ^= 1;         // after the node
        Assert.assertEquals(s, sum(data, offset, length));
    }
}
