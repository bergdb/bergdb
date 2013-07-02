package bergdb.common;

import java.util.Random;

import bergdb.nanotest.Assert;
import bergdb.nanotest.T;

/**
 * <p>This class implements Salsa20 encryption with a 256 bit key.
 * Salsa20 encrypts in 64 byte blocks. It supports access to the encrypted
 * stream at each 64 byte block. It is a stream cipher, so it can write 
 * bytes one by one.</p>
 * 
 * <p>Original code idea taken from estreamJ (http://www.hotpixel.net/software.html).</p>
 * 
 * @author Frans Lundberg
 */
public class Salsa {
    public static final int BLOCK_SIZE = 64;
    private static final byte[] sigma = "expand 32-byte k".getBytes();
    private final int[] input = new int[16];
    private final byte[] output = new byte[64];
    private final int[] x = new int[16];    // 64 bytes of temporary data used by core().
    
    public Salsa(byte[] nonce, byte[] key) {
        if (nonce == null) {
            throw new IllegalArgumentException("nonce == null not allowed");
        }
        
        if (key == null) {
            throw new IllegalArgumentException("key == null not allowed");
        }
        
        setupNonce(nonce);
        setupKey(key);
    }
    
    /**
     * The Salsa20 core, see http://cr.yp.to/salsa20.html.
     */
    private void core() {
        // Processes 64 bytes in this.input to 64 bytes in this.output.
        
        final int[] x = this.x;
        int i;
        int s;
        
        System.arraycopy(input, 0, x, 0, x.length);

        for (i = 20; i > 0; i -= 2) {
            s = x[ 0] + x[12]; x[ 4] ^= (s <<  7) | (s >>> (32 -  7));
            s = x[ 4] + x[ 0]; x[ 8] ^= (s <<  9) | (s >>> (32 -  9));
            s = x[ 8] + x[ 4]; x[12] ^= (s << 13) | (s >>> (32 - 13));
            s = x[12] + x[ 8]; x[ 0] ^= (s << 18) | (s >>> (32 - 18));
            s = x[ 5] + x[ 1]; x[ 9] ^= (s <<  7) | (s >>> (32 -  7));
            s = x[ 9] + x[ 5]; x[13] ^= (s <<  9) | (s >>> (32 -  9));
            s = x[13] + x[ 9]; x[ 1] ^= (s << 13) | (s >>> (32 - 13));
            s = x[ 1] + x[13]; x[ 5] ^= (s << 18) | (s >>> (32 - 18));
            s = x[10] + x[ 6]; x[14] ^= (s <<  7) | (s >>> (32 -  7));
            s = x[14] + x[10]; x[ 2] ^= (s <<  9) | (s >>> (32 -  9));
            s = x[ 2] + x[14]; x[ 6] ^= (s << 13) | (s >>> (32 - 13));
            s = x[ 6] + x[ 2]; x[10] ^= (s << 18) | (s >>> (32 - 18));
            s = x[15] + x[11]; x[ 3] ^= (s <<  7) | (s >>> (32 -  7));
            s = x[ 3] + x[15]; x[ 7] ^= (s <<  9) | (s >>> (32 -  9));
            s = x[ 7] + x[ 3]; x[11] ^= (s << 13) | (s >>> (32 - 13));
            s = x[11] + x[ 7]; x[15] ^= (s << 18) | (s >>> (32 - 18));
            s = x[ 0] + x[ 3]; x[ 1] ^= (s <<  7) | (s >>> (32 -  7));
            s = x[ 1] + x[ 0]; x[ 2] ^= (s <<  9) | (s >>> (32 -  9));
            s = x[ 2] + x[ 1]; x[ 3] ^= (s << 13) | (s >>> (32 - 13));
            s = x[ 3] + x[ 2]; x[ 0] ^= (s << 18) | (s >>> (32 - 18));
            s = x[ 5] + x[ 4]; x[ 6] ^= (s <<  7) | (s >>> (32 -  7));
            s = x[ 6] + x[ 5]; x[ 7] ^= (s <<  9) | (s >>> (32 -  9));
            s = x[ 7] + x[ 6]; x[ 4] ^= (s << 13) | (s >>> (32 - 13));
            s = x[ 4] + x[ 7]; x[ 5] ^= (s << 18) | (s >>> (32 - 18));
            s = x[10] + x[ 9]; x[11] ^= (s <<  7) | (s >>> (32 -  7));
            s = x[11] + x[10]; x[ 8] ^= (s <<  9) | (s >>> (32 -  9));
            s = x[ 8] + x[11]; x[ 9] ^= (s << 13) | (s >>> (32 - 13));
            s = x[ 9] + x[ 8]; x[10] ^= (s << 18) | (s >>> (32 - 18));
            s = x[15] + x[14]; x[12] ^= (s <<  7) | (s >>> (32 -  7));
            s = x[12] + x[15]; x[13] ^= (s <<  9) | (s >>> (32 -  9));
            s = x[13] + x[12]; x[14] ^= (s << 13) | (s >>> (32 - 13));
            s = x[14] + x[13]; x[15] ^= (s << 18) | (s >>> (32 - 18));
        }
        
        for (i = 0; i < 16; i++) {
            writeIntLE(x[i] + input[i], output, i << 2);
        }
    }
    
    private long appendPos = 0;
    
    /**
     * Appends more data to process.
     * This method handles appending any size of input data.
     */
    public void append(byte[] in, int inOffset, byte[] out, int outOffset, int len) {
        // This method adds functionality of adding bytes to process independent
        // of 64-byte block size boundaries.
        
        int blockPos = (int) (appendPos % BLOCK_SIZE);
        int lenDone = 0;
        
        if (blockPos != 0) {
            // Handles rest of block already processed with core().
            
            for (int i = blockPos; i < BLOCK_SIZE; i++) {
                if (lenDone == len) break;
                out[outOffset + lenDone] = (byte)(in[inOffset + lenDone] ^ output[i]);
                lenDone++;
            }
            
            this.appendPos += lenDone;
            
            if (lenDone == len) {
                return;
            }
            
            inOffset += lenDone;
            outOffset += lenDone;
            len -= lenDone;
        }
        
        // process() inlined, handles 64-byte blocks of data.
        
        int i, c;
        
        if (len > 0) {
            while (true) {
                core();
                if (0 == ++input[8]) {
                    input[9]++;      // We don't stop at 2^70 bytes.
                }
                
                c = (len <= 64) ? len : 64;
                for (i = 0; i < c; i++) {
                    out[outOffset + i] = (byte)(in[inOffset + i] ^ output[i]);
                }
                appendPos += c;
                len -= 64;
                if (len < 1) {
                    break;
                }
                inOffset += 64;
                outOffset += 64;
            }
        }
    }

    /**
     * in[inOffset] and out[outOffset] are assumed to be at 64-byte block start.
     * Only last len may be less than 64.
     * 
     * @deprecated 130506 Use append() instead.
     */
    public void process(byte[] in, int inOffset, byte[] out, int outOffset, int len) {
        int i, c;
        
        if (len > 0) {
            while (true) {
                core();
                if (0 == ++input[8]) {
                    input[9]++;      // We don't stop at 2^70 bytes.
                }
                
                c = (len <= 64) ? len : 64;
                for (i = 0; i < c; i++) {
                    out[outOffset + i] = (byte)(in[inOffset + i] ^ output[i]);
                }
                appendPos += c;
                len -= 64;
                if (len < 1) {
                    break;
                }
                inOffset += 64;
                outOffset += 64;
            }
        }
    }

    /**
     * The 256-bit key (32 bytes).
     */
    private void setupKey(byte[] key) {
        byte[] constants;
        int ofs = 0;
        
        if (key.length != 32) {
            throw new IllegalArgumentException("bad key size, should be " +
                    "32 bytes, was " + key.length + " bytes.");
        }
        
        this.input[1] = readIntLE(key, ofs     );
        this.input[2] = readIntLE(key, ofs +  4);
        this.input[3] = readIntLE(key, ofs +  8);
        this.input[4] = readIntLE(key, ofs + 12);
        
        ofs += 16;
        constants = sigma;
        
        this.input[11] = readIntLE(key, ofs +  0);
        this.input[12] = readIntLE(key, ofs +  4);
        this.input[13] = readIntLE(key, ofs +  8);
        this.input[14] = readIntLE(key, ofs + 12);
        
        this.input[ 0] = readIntLE(constants,  0);
        this.input[ 5] = readIntLE(constants,  4);
        this.input[10] = readIntLE(constants,  8);  
        this.input[15] = readIntLE(constants, 12);  
    }

    private void setupNonce(byte[] nonce) {
        if (nonce.length != 8) {
            throw new IllegalArgumentException("Expected nonce to be 8 bytes," +
                    " was " + nonce.length + ".");
        }
        this.input[6] = readIntLE(nonce, 0);
        this.input[7] = readIntLE(nonce, 4);
        this.input[8] = 0; 
        this.input[9] = 0;
    }
    
    public void setupBlockCounter(long counter) {
        long two32 = (long)1 << 32;
        this.input[8] = (int) (counter % two32);
        this.input[9] = (int) (counter / two32);
        this.appendPos = counter * BLOCK_SIZE;
    }
    
    private final static void writeIntLE(int value, byte[] data, int ofs) {
        data[ofs    ] = (byte)(value       );
        data[ofs + 1] = (byte)(value >>>  8);
        data[ofs + 2] = (byte)(value >>> 16);
        data[ofs + 3] = (byte)(value >>> 24);
    }
    
    private final static int readIntLE(byte[] data, int ofs) {
        return ( data[ofs + 3]         << 24) |
               ((data[ofs + 2] & 0xff) << 16) |
               ((data[ofs + 1] & 0xff) <<  8) |
                (data[ofs    ] & 0xff);
    }
    
    // ======== Tests ========
    
    @T
    public static void testBasic() {
        Random r = new Random(0);
        byte[] nonce = new byte[8];
        byte[] key = new byte[32];
        byte[] dataIn = new byte[10 * 1024];
        byte[] dataOut = new byte[10 * 1024];
        byte[] dataBack = new byte[10 * 1024];
        
        r.nextBytes(key);
        r.nextBytes(nonce);
        r.nextBytes(dataIn);
        
        Salsa c = new Salsa(nonce, key);
        c.append(dataIn, 0, dataOut, 0, dataIn.length);
        
        c = new Salsa(nonce, key);
        c.append(dataOut, 0, dataBack, 0, dataOut.length);
        
        Assert.assertArrayEquals("arrays compared", dataIn, dataBack);
    }
    
    @T
    public static void testStream7() {
        // Encrypting/decrypting a byte array that is 7 bytes long.
        
        byte[] nonce = new byte[8];
        byte[] key = new byte[32];
        Random r = new Random(0);
        byte[] dataIn = new byte[7];
        byte[] dataOut = new byte[7];
        byte[] dataBack = new byte[7];
        
        r.nextBytes(key);
        r.nextBytes(nonce);
        r.nextBytes(dataIn);
        
        Salsa c = new Salsa(nonce, key);
        c.append(dataIn, 0, dataOut, 0, dataIn.length);
        
        c = new Salsa(nonce, key);
        c.append(dataOut, 0, dataBack, 0, dataOut.length);
        
        Assert.assertArrayEquals("arrays compared", dataIn, dataBack);
    }
    
    @T
    public static void testRandomAccess() {
        Salsa c;
        byte[] nonce = new byte[8];
        byte[] key = new byte[32];
        Random r = new Random(0);
        byte[] clearText = new byte[1024];
        byte[] cipherText = new byte[clearText.length];
        byte[] expectedClear = new byte[clearText.length];
        
        r.setSeed(0);
        r.nextBytes(key);
        r.nextBytes(nonce);
        r.nextBytes(clearText);
        
        c = new Salsa(nonce, key);
        c.setupBlockCounter(0);
        c.append(clearText, 0, cipherText, 0, clearText.length);
        c.setupBlockCounter(3);
        
        int offset = 3*64;        // 64 = one Salsa block
        expectedClear = new byte[clearText.length];
        c.append(cipherText, offset, expectedClear, offset, 
                  cipherText.length - offset);
        
        for (int i = offset; i < cipherText.length; i++) {
            Assert.assertEquals("byte" + i, clearText[i], expectedClear[i]);
        }
    }
    
    @T
    public static void testInPlace() {
        Salsa c;
        byte[] nonce = new byte[8];
        byte[] key = new byte[32];
        Random r = new Random(0);
        byte[] text = new byte[1024];
        byte[] clearCopy;
                                     
        r.setSeed(0);
        r.nextBytes(key);
        r.nextBytes(nonce);
        r.nextBytes(text);
        clearCopy = text.clone();
        
        c = new Salsa(nonce, key);
        c.setupBlockCounter(0);
        c.append(text, 0, text, 0, text.length);

        c = new Salsa(nonce, key);
        c.setupBlockCounter(0);
        c.append(text, 0, text, 0, text.length);
        
        Assert.assertArrayEquals("in place copy", clearCopy, text);
    }
    
    @T
    public static void testNot64() {
        //
        // Encrypts some data with a size not a multiple of 64, restarts encryption to continue.
        // Writes 75 bytes, creates a new Salsa object, writes 75 more bytes.
        // Finally create a Salsa object to decrypt the whole data.
        //
        
        byte[] data = new byte[150];
        for (int i = 0; i < data.length; i++) {
            data[i] = (byte) (i % 100);
        }
        
        Random r = new Random(0);
        byte[] nonce = new byte[8];
        byte[] key = new byte[32];
        r.nextBytes(key);
        
        byte[] out = new byte[data.length];
        
        Salsa s0 = new Salsa(nonce, key);
        s0.append(data, 0, out, 0, 75);
        
        // We wrote 75 bytes, lets write 75 more in another Salsa object.
        // We must re-process some bytes.
        
        Salsa s1 = new Salsa(nonce, key);
        s1.setupBlockCounter(1);
        s1.append(data, 1*64, out, 64, data.length - 64);
        
        // Now, decrypt all 150 bytes with a new Salsa object.
        
        byte[] dataBack = new byte[data.length];
        Salsa s2 = new Salsa(nonce, key);
        s2.append(out, 0, dataBack, 0, out.length);
        
        // Compare
        
        Assert.assertArrayEquals(data, dataBack);
    }
    
    @T
    public static void testNot64b() {
        //
        // Encrypts some data with a size not a multiple of 64, restarts encryption to continue.
        // Writes 75 bytes, creates a new Salsa object, writes 75 more bytes.
        // Finally create a Salsa object to decrypt the whole data.
        //
        
        byte[] data = new byte[150];
        for (int i = 0; i < data.length; i++) {
            data[i] = (byte) (i % 100);
        }
        
        Random r = new Random(0);
        byte[] nonce = new byte[8];
        byte[] key = new byte[32];
        r.nextBytes(key);
        
        byte[] out = new byte[data.length];
        
        Salsa s0 = new Salsa(nonce, key);
        s0.append(data, 0, out, 0, 75);
        
        // We wrote 75 bytes, lets write 75 more in another Salsa object.
        // We must re-process some bytes.
        // We assume we only have data[>=75] available. data[64..74] must be read from 'out'.
        
        Salsa sr = new Salsa(nonce, key);
        sr.setupBlockCounter(1);
        byte[] block = new byte[64];
        sr.append(out, 64, block, 0, 11);
        System.arraycopy(data, 75, block, 11, 64 - 11);    
        
        // block created from data read with sr and from data.
        
        Salsa s1 = new Salsa(nonce, key);
        s1.setupBlockCounter(1);
        s1.append(block, 0, out, 64, 64);       // After this line, we at offset 128
        s1.append(data, 128, out, 128, data.length - 128);
        
        // Now, decrypt all 150 bytes with a new Salsa object.
        
        byte[] dataBack = new byte[data.length];
        Salsa s2 = new Salsa(nonce, key);
        s2.append(out, 0, dataBack, 0, out.length);
        
        // Compare
        
        Assert.assertArrayEquals(data, dataBack);
    }
    
    @T
    public static void testFirst3() {
        byte[] data = new byte[100];
        for (int i = 0; i < data.length; i++) {
            data[i] = (byte) (i % 100);
        }
        
        byte[] data3 = new byte[3];
        for (int i = 0; i < data3.length; i++) {
            data3[i] = (byte) (i % 100);
        }
        
        Random r = new Random(0);
        byte[] nonce = new byte[8];
        byte[] key = new byte[32];
        r.nextBytes(nonce);
        r.nextBytes(key);
        
        byte[] out0 = new byte[3];
        byte[] out1 = new byte[data.length];
        
        Salsa s0 = new Salsa(nonce, key);
        s0.append(data3, 0, out0, 0, 3);
        String res0 = Util.toHexString(out0, 0, 3);
        
        Salsa s1 = new Salsa(nonce, key);
        s1.append(data, 0, out1, 0, data.length);
        String res1 = Util.toHexString(out1, 0, 3);
        
        Assert.assertEquals("first 3 bytes", res0, res1);
    }
    
    public static void testAppend1() {
        Random r = new Random(0);
        byte[] nonce = new byte[8];
        byte[] key = new byte[32];
        byte[] data = new byte[2];
        byte[] out = new byte[2];
        byte[] data2 = new byte[2];
        r.nextBytes(nonce);
        r.nextBytes(key);
        r.nextBytes(data);
        
        Salsa s0 = new Salsa(nonce, key);
        s0.append(data, 0, out, 0, 1);
        s0.append(data, 1, out, 1, 1);
        
        s0.setupBlockCounter(0);
        s0.append(out, 0, data2, 0, 2);
        
        Assert.assertArrayEquals(data, data2);
    }
    
    public static void testAppendOneByteAtATime() {
        Random r = new Random(0);
        byte[] nonce = new byte[8];
        byte[] key = new byte[32];
        byte[] data = new byte[70];
        byte[] out = new byte[70];
        byte[] data2 = new byte[70];
        r.nextBytes(nonce);
        r.nextBytes(key);
        r.nextBytes(data);
        
        Salsa s0 = new Salsa(nonce, key);
        for (int i = 0; i < data.length; i++) {
            s0.append(data, i, out, i, 1);
        }
        
        Salsa s1 = new Salsa(nonce, key);
        s1.append(out, 0, data2, 0, out.length);
        
        Assert.assertArrayEquals(data, data2);
    }
    
    public static void main(String[] args) {
        testFirst3();
    }
}

/*
== 130504 Frans ==
Added method append(). More flexible then process(), handles non-64 appends.

== Old source history ==
- Original code idea from estreamJ (http://www.hotpixel.net/software.html).
- Only supports 32 byte (256 bit) key. Fine with me :)
- Mode removed since not used.
- Offset for key and nonce arrays removed
- setupBlockCounter added.
- removed reset, changed code standard
- Changed to final fields.
- Added Nanotests to this source file.
- Created constructor that takes nonce and key.
*/