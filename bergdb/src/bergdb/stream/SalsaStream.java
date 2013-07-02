package bergdb.stream;

import java.io.IOException;
import java.util.Random;

import bergdb.common.Salsa;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;

/**
 * A decorator for an AppendOnlyStream that adds Salsa20 encryption to the stream.
 * 
 * @author Frans Lundberg
 */
public class SalsaStream implements AppendOnlyStream {
    private final AppendOnlyStream stream;
    private final Salsa encrypt;
    private final Salsa decrypt;
    private long length;
    private final Object readLock = new Object();
    
    /**
     * Creates an instead by wrapping an underlying stream.
     * 
     * @param stream  The underlying stream to append encrypted data to.
     * @param nonce   8-byte nonce.
     * @param key     32-byte key.
     * @throws IOException If 'stream' needs to be read and the read throws an IOException.
     */
    public SalsaStream(AppendOnlyStream stream, byte[] nonce, byte[] key) throws IOException {
        if (stream == null) {
            throw new IllegalArgumentException("stream == null not allowed");
        }
        
        this.stream = stream;
        
        length = stream.getLength();
        int blockOffset = (int) (length % Salsa.BLOCK_SIZE);
        long p0 = length - blockOffset;    // stream position of beginning of block
        byte[] lastBlock = new byte[blockOffset];
        
        if (lastBlock.length > 0) {
            stream.read(p0, lastBlock, 0, lastBlock.length);
        }
        
        Salsa salsa = new Salsa(nonce, key);
        salsa.setupBlockCounter(p0 / Salsa.BLOCK_SIZE);
        salsa.append(lastBlock, 0, lastBlock, 0, lastBlock.length);    // in-place decryption
        
        byte[] outDummy = new byte[lastBlock.length];
        encrypt = new Salsa(nonce, key);
        encrypt.setupBlockCounter(length / Salsa.BLOCK_SIZE);
        encrypt.append(lastBlock, 0, outDummy, 0, lastBlock.length);
        
        decrypt = new Salsa(nonce, key);
        
        synchronized (readLock) {}    // Could be needed, in theory.
    }

    public long getLength() {
        return length;
    }

    public long getFirstPos() {
        return stream.getFirstPos();
    }

    public void read(long position, byte[] dest, int destOffset, int length) throws IOException {
        synchronized (readLock) {
            long blockPos = (position / Salsa.BLOCK_SIZE) * Salsa.BLOCK_SIZE;
            long blockOffset = position % Salsa.BLOCK_SIZE;
            assert blockPos * Salsa.BLOCK_SIZE + blockOffset == position;
            long lengthToRead = blockOffset + length;
            if (lengthToRead > Integer.MAX_VALUE) {
                throw new Error("lengthToRead is too large: " + lengthToRead + ".");
            }
            
            byte[] b = new byte[(int) lengthToRead];  // Should be fast stack allocation.
            stream.read(blockPos, b, 0, b.length);
            
            decrypt.setupBlockCounter(blockPos / Salsa.BLOCK_SIZE);
            decrypt.append(b, 0, b, 0, b.length);     // in-place decryption
            
            assert length <= b.length;
            assert position >= blockPos;
            
            int diff = (int) (position - blockPos);
            System.arraycopy(b, diff, dest, destOffset, length);
        }
    }

    public void append(byte[] source, int sourceOffset, int length) throws IOException {
        byte[] b = new byte[length];    // We hope for high performance with stack allocation
        encrypt.append(source, sourceOffset, b, 0, length);
        stream.append(b, 0, length);
    }

    public void pretruncate(long position) throws IOException {
        stream.pretruncate(position);
    }

    public void seekFirstPos(long position) throws IOException {
        stream.seekFirstPos(position);
    }

    public void close() throws IOException {
        stream.close();
    }
    
    @T
    public static void test0() throws IOException {
        // Writes 128 bytes of data to SalsaStream and reads it back.
        
        byte[] data = new byte[128];
        for (int i = 0; i < data.length; i++) {
            data[i] = (byte) i;
        }
        
        byte[] key = new byte[32];
        key[12] = 12;
        
        MemoryStream m = new MemoryStream();
        SalsaStream s = new SalsaStream(m, new byte[8], key);
        
        s.append(data, 0, data.length);
        
        byte[] data2 = new byte[128];
        s.read(0, data2, 0, data.length);
        
        Assert.assertArrayEquals(data, data2);
    }
    
    @T
    public static void test1() throws IOException {
        // Writes 128 bytes of data to SalsaStream and reads it back using another Salsa object.
        
        Random r = new Random(0);
        byte[] data = new byte[128];
        r.nextBytes(data);
        byte[] nonce = new byte[8];
        r.nextBytes(nonce);
        byte[] key = new byte[32];
        r.nextBytes(key);
        
        MemoryStream m = new MemoryStream();
        SalsaStream s = new SalsaStream(m, nonce, key);
        s.append(data, 0, data.length);
        
        byte[] data2 = new byte[128];
        SalsaStream s2 = new SalsaStream(m, nonce, key);
        s2.read(0, data2, 0, data2.length);
        
        Assert.assertArrayEquals(data, data2);
    }
    
    @T
    public static void testMultiAppend() throws IOException {
        Random r = new Random(0);
        byte[] data = new byte[64];
        r.nextBytes(data);
        byte[] nonce = new byte[8];
        r.nextBytes(nonce);
        byte[] key = new byte[32];
        r.nextBytes(key);
        
        MemoryStream m = new MemoryStream();
        SalsaStream s = new SalsaStream(m, nonce, key);
        
        for (int i = 0; i < 32; i++) {
            s.append(data, i*2, 2);
        }
        
        byte[] data2 = new byte[data.length];
        s.read(0, data2, 0, data.length);
        Assert.assertArrayEquals(data, data2);
    }
    
    @T
    public static void testReadPartOfBlock1() throws IOException {
        // Writes 128 bytes of data to SalsaStream and reads part of it back.
        
        byte[] data = new byte[128];
        for (int i = 0; i < data.length; i++) {
            data[i] = (byte) i;
        }
        
        byte[] key = new byte[32];
        key[12] = 12;
        
        MemoryStream m = new MemoryStream();
        SalsaStream s = new SalsaStream(m, new byte[8], key);
        
        s.append(data, 0, data.length);
        
        byte[] data2 = new byte[30];
        s.read(40, data2, 0, data2.length);
        
        byte[] data3 = new byte[30];
        System.arraycopy(data, 40, data3, 0, 30);
        
        Assert.assertArrayEquals(data3, data2);
    }
    
    @T
    public static void testNon64a() throws IOException {
        Random r = new Random(123);
        byte[] data = new byte[100];
        r.nextBytes(data);
        byte[] nonce = new byte[8];
        r.nextBytes(nonce);
        byte[] key = new byte[32];
        r.nextBytes(key);
        
        // Creates SalsaStream and adds 100 bytes.
        
        MemoryStream m = new MemoryStream();
        SalsaStream s = new SalsaStream(m, nonce, key);
        s.append(data, 0, 100);
        
        // Reopens and reads the data. Verifies it.
        
        byte[] data2 = new byte[100];
        s = new SalsaStream(m, nonce, key);
        s.read(0, data2, 0, 100);
        
        Assert.assertArrayEquals(data, data2);
    }
    
    @T
    public static void testNon64b() throws IOException {
        // Multiple append operations. Appends 5+5 bytes, read by another Salsa object.
        
        Random r = new Random(0);
        byte[] data = new byte[10];
        r.nextBytes(data);
        byte[] nonce = new byte[8];
        r.nextBytes(nonce);
        byte[] key = new byte[32];
        r.nextBytes(key);
        
        // Creates SalsaStream and adds 5+5 bytes.
        
        MemoryStream m = new MemoryStream();
        SalsaStream s = new SalsaStream(m, nonce, key);
        s.append(data, 0, 5);
        s.append(data, 5, 5);
        
        // Reopens and reads the data. Verifies it.
        
        byte[] data2 = new byte[10];
        s = new SalsaStream(m, nonce, key);
        s.read(0, data2, 0, 10);
        
        Assert.assertArrayEquals(data, data2);
    }
    
    @T
    public static void testNon64c() throws IOException {
        // Writes 100 + 100 bytes of data to SalsaStream and reads it back.
        
        Random r = new Random(123);
        byte[] data = new byte[200];
        r.nextBytes(data);
        byte[] nonce = new byte[8];
        r.nextBytes(nonce);
        byte[] key = new byte[32];
        r.nextBytes(key);
        
        // Creates SalsaStream and adds 100 bytes.
        
        MemoryStream m = new MemoryStream();
        SalsaStream s = new SalsaStream(m, nonce, key);
        s.append(data, 0, 100);
        
        // "Reopens" in new SalsaStream object and appends 100 more bytes.
        
        s = new SalsaStream(m, nonce, key);
        s.append(data, 100, 100);
        
        // Reopens and reads all data. Verifies it.
        
        byte[] data2 = new byte[200];
        s = new SalsaStream(m, nonce, key);
        s.read(0, data2, 0, 200);
        
        Assert.assertArrayEquals(data, data2);
    }
}
