package bergdb.core;

import bergdb.common.Bytes;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * Fast 16-bit checksums for stored nodes; Fletcher-16 is used.
 * 
 * @author Frans Lundberg
 */
public class NodeChecksum {

    public static int sum(byte[] data, int offset, int length) {
        int sum1 = 0;
        int sum2 = 0;
        int end = offset + length;
        
        for (int i = offset; i < end; i++) {
            // "data[i] & 0x000000ff" is Bytes.unsigned() inlined.
            int dataValue = data[i] & 0x000000ff;
            
            sum1 = (sum1 + dataValue) % 255;
            sum2 = (sum1 + sum2) % 255;
        }
        
        return sum1 | (sum2 << 8);
    }
    
    /**
     * Checksum computation like "sum", but two bytes in data (at offset "replaceOffset")
     * should be considered equal to zero by this method.
     */
    public static int sumWithZeroReplace(byte[] data, int offset, int length, int replaceOffset) {
        int sum1 = 0;
        int sum2 = 0;
        int dataValue;
        final int end = offset + length;
        final int replaceOffset2 = replaceOffset + 1;
        
        for (int i = offset; i < end; i++) {
            // "data[i] & 0x000000ff" is Bytes.unsigned() inlined.
            dataValue = data[i] & 0x000000ff;
            
            if (i == replaceOffset || i == replaceOffset2) {
                dataValue = 0;
            }
            
            sum1 = (sum1 + dataValue) % 255;
            sum2 = (sum1 + sum2) % 255;
        }
        
        return sum1 | (sum2 << 8);
    }
    
    /**
     * Fletcher-16 for data stored in long array. Little-endian first byte order.
     * Only whole longs (8-byte) are supported.
     */
    public static int sum(long[] data, int offset, int length) {
        int sum1 = 0;
        int sum2 = 0;
        int end = offset + length;
        
        for (int i = offset; i < end; i++) {
            long l = data[i];
            
            for (int j = 0; j < 8; j++) {
                int dataValue = (int) (l & 0x000000ff);
                sum1 = (sum1 + dataValue) % 255;
                sum2 = (sum1 + sum2) % 255;
                l = l >>> 8;
            }
        }
        
        return sum1 | (sum2 << 8);
    }
    
    
    
    // ======== Testing ========
    
    @Nano private static void test0() {
        // Example from https://en.wikipedia.org/wiki/Fletcher%27s_checksum
        
        byte[] data = new byte[]{0x01, 0x02};
        int sum = sum(data, 0, data.length);
        
        Assert.assertEquals(0x0403, sum);
    }
    
    @Nano private static void testWithLongArray1() {
        byte[] data = new byte[]{0x01, 0x02, (byte) 0xff, 0x10, 0x00, 0x01, 0x02, 0x03};
        int sum1 = sum(data, 0, data.length);
        
        long l = Bytes.bytesToLongLE(data, 0);
        int sum2 = sum(new long[]{l}, 0, 1);
        
        Assert.assertEquals(sum1, sum2);
    }
    
    @Nano private static void testWithLongArray2() {
        byte[] data = new byte[]{
                0x01, 0x02, (byte) 0xff, 0x10, 0x20, 0x21, 0x23, 0x24,
                (byte) 0xff, (byte) 0xff, (byte) 0xff, (byte) 0xff, 0x0f, 0x0f, 0x0f, 0x0f};
        
        int sum1 = sum(data, 0, data.length);
        
        long[] longs = new long[]{Bytes.bytesToLongLE(data, 0), Bytes.bytesToLongLE(data, 8)};
        int sum2 = sum(longs, 0, 2);
        
        Assert.assertEquals(sum1, sum2);
    }
    
    @Nano private static void testZeroReplace() {
        byte[] data1 = new byte[]{0x01, 0x02, (byte) 0xff, 0x10, 0x00, 0x01, 0x02, 0x03};
        byte[] data2 = new byte[]{0x01, 0x00,        0x00, 0x10, 0x00, 0x01, 0x02, 0x03};
        
        int sum1 = sumWithZeroReplace(data1, 0, data1.length, 1);
        int sum2 = sum(data2, 0, data2.length);
        
        Assert.assertEquals(sum1, sum2);
    }
}
