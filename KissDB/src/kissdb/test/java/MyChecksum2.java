package kissdb.test.java;

import java.util.Random;
import java.util.zip.Checksum;

import kissdb.common.Bytes;

/**
 * Very simple 8-bit checksum. Bytes are just XORed together but a 8-byte bit pattern is used
 * in the XOR too to introduce some position-dependency.
 * Performs well on both byte arrays and long arrays.
 * 
 * @author Frans Lundberg
 */
public class MyChecksum2 implements Checksum {
    
    static final int[] pattern = new int[] {0x34, 0x11, 0xf0, 0x33, 0x55, 0xfe, 0x45, 0x01};
    static final byte[] bpattern = new byte[] {0x34, 0x11, (byte) 0xf0, 0x33, 0x55, (byte) 0xfe, 0x45, 0x01};
    static final long p = Bytes.bytesToLongLE(bpattern, 0);
    
    /**
     * Computes a 8-bit checksum.
     * 
     * @param buffer  The byte buffer to compute the checksum on.
     * @param offset  Offset to start at in 'buffer'.
     */
    public static final int compute(byte[] buffer, int offset, int size) {
        final int end = offset + size;
        int sum = 0;
        int pIndex = 0;
        
        while (offset < end) {
            sum ^= (buffer[offset] ^ pattern[pIndex % pattern.length]);
            pIndex++;
            offset++;
        }
        
        return sum & 0x000000ff;
    }
    
    public static final int compute(long[] buffer, int offset, int size) {
        final int end = offset + size;
        long sum = 0;
        
        while (offset < end) {
            sum ^= (buffer[offset] ^ p);
            offset++;
        }
        
        long s =   (sum >>> (0*8)) ^ (sum >>> (1*8)) 
                 ^ (sum >>> (2*8)) ^ (sum >>> (3*8)) 
                 ^ (sum >>> (4*8)) ^ (sum >>> (5*8)) 
                 ^ (sum >>> (6*8)) ^ (sum >>> (7*8));
        
        return (int) (s & 0x00ff);
    }

    private int sum;
    private int pIndex;
    
    public MyChecksum2() {
        reset();
    }
    
    public void update(int b) {
        sum ^= (b ^ pattern[pIndex % pattern.length]);
        pIndex++;
    }

    public void update(byte[] b, int off, int len) {
        for (int i = 0; i < len; i++) {
            sum ^= b[off + i] ^ pattern[pIndex % pattern.length];
            pIndex++;
        }
    }

    public long getValue() {
        return sum & 0xff;
    }

    public void reset() {
        sum = 0;
        pIndex = 0;
    }
    
    public static void main(String[] args) {
        long[] data = new long[40];
        long processed = 0;
        long t0 = System.nanoTime();
        double time = 1.0;
        int sum = 0;
        
        Random r = new Random(1);
        for (int i = 0; i < data.length; i++) {
            data[i] = r.nextLong();
        }
        
        while (true) {
            int n = 100;
            for (int i = 0; i < n; i++) {
                sum += MyChecksum2.compute(data, 0, data.length);
            }
            
            processed += n * data.length * 8;
            time = (System.nanoTime() - t0) * 1e-9;
            if (time > 2.0) {
                break;
            }
        }
        
        System.out.println("sum: " + sum);
        System.out.println("MBPerSec: " + (processed * 1e-6 / time));
    }
}
