package bergdb.stream;

import java.io.IOException;
import java.util.Random;

import bergdb.common.Salsa;
import bergdb.common.Util;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;

/**
 * A decorator for an AppendOnlyStream that adds Salsa20 encryption to 
 * the underlying stream.
 * 
 * <p>Internal, not API: release 2026.4 has no encryption (bergdb 020-28). The class is kept,
 * with its tests, for a later design (bergdb 017-10): the keystream depends only on the key,
 * the nonce and the position in the stream, so two writes at one position with one key reuse
 * it (020-24-07, U7-1), and nothing checks the integrity of the bytes (U7-3). Until 2026.3
 * the Pub API's crypto key made one around the database's stream; since 2026.4 only
 * DatabaseBuilderImp's internal cryptoKey(), for BergDB's tests, does.</p>
 * 
 * @author Frans Lundberg
 */
public class SalsaStream implements AppendOnlyStream {
    private final AppendOnlyStream stream;
    private final Salsa encrypt;
    private final Salsa decrypt;
    private final Object readLock = new Object();
    
    /**
     * The encrypted bytes of an append, before they go to the stream under this one. It grows
     * to the longest append so far, up to MAX_APPEND_BUFFER (bergdb 020-24-07, U7-2).
     */
    private byte[] appendBuffer = new byte[100*1024];
    
    /**
     * The longest append that goes to the stream under this one as one append; a longer one
     * goes in parts of this length (bergdb 020-24-07, U7-2). The database's appends are its
     * write buffer's flushes, at most half of the buffer: 5 MB by default.
     */
    static final int MAX_APPEND_BUFFER = 16*1024*1024;
    
    /**
     * The key's line of created.txt (Db.writeCreatedTxt): its name and algorithm with the key
     * data masked, as "3fa2c901-salsa-****" (bergdb 020-28).
     */
    private final String keyInfo;
    
    /**
     * Creates an instead by wrapping an underlying stream.
     * 
     * @param stream  The underlying stream to append encrypted data to.
     * @param nonce   8-byte nonce.
     * @param key     32-byte key.
     * @throws IOException If 'stream' needs to be read and the read throws an IOException.
     */
    public SalsaStream(AppendOnlyStream stream, byte[] nonce, byte[] key) throws IOException {
        this(stream, nonce, key, null);
    }
    
    /**
     * Creates an instance as SalsaStream(stream, nonce, key) does, with the key's line of
     * created.txt (bergdb 020-28).
     * 
     * @param keyInfo  The key's name and algorithm with the key data masked, as
     *      "3fa2c901-salsa-****", for created.txt; or null for "unnamed-salsa-****".
     * @throws IOException If 'stream' needs to be read and the read throws an IOException.
     */
    public SalsaStream(AppendOnlyStream stream, byte[] nonce, byte[] key, String keyInfo) 
            throws IOException {
        this.keyInfo = keyInfo == null ? "unnamed-salsa-****" : keyInfo;
        if (stream == null) {
            throw new IllegalArgumentException("stream == null not allowed");
        }
        
        if (nonce == null) {
            throw new IllegalArgumentException("nonce == null not allowed");
        }
        
        if (key == null) {
            throw new IllegalArgumentException("key == null not allowed");
        }
        
        byte[] nonceCopy = nonce.clone();
        nonce = null;
        byte[] keyCopy = key.clone();
        key = null;
        this.stream = stream;
        
        final long length = stream.getLength();
        int blockOffset = (int) (length % Salsa.BLOCK_SIZE);
        long p0 = length - blockOffset;    // stream position of beginning of block
        byte[] lastBlock = new byte[blockOffset];
        
        if (lastBlock.length > 0) {
            stream.read(p0, lastBlock, 0, lastBlock.length);
        }
        
        Salsa salsa = new Salsa(nonceCopy, keyCopy);
        salsa.setupBlockCounter(p0 / Salsa.BLOCK_SIZE);
        salsa.append(lastBlock, 0, lastBlock, 0, lastBlock.length);    // in-place decryption
        
        byte[] outDummy = new byte[lastBlock.length];
        encrypt = new Salsa(nonceCopy, keyCopy);
        encrypt.setupBlockCounter(length / Salsa.BLOCK_SIZE);
        encrypt.append(lastBlock, 0, outDummy, 0, lastBlock.length);
        
        decrypt = new Salsa(nonceCopy, keyCopy);
        
        synchronized (readLock) {}    // Could be needed, in theory.
    }
    
    /**
     * The key's line of created.txt: its name and algorithm with the key data masked (bergdb
     * 020-28).
     */
    public String getKeyInfo() {
        return keyInfo;
    }
    
    public AppendOnlyStream getUnderlyingStream() {
        return stream;
    }

    /**
     * The underlying stream's length, which counts what this stream appends (2026-10-25,
     * bergdb 005-45: it was the length when this stream was made).
     */
    public long getLength() {
        return stream.getLength();
    }

    public long getFirstPos() {
        return stream.getFirstPos();
    }

    /**
     * Reads and decrypts. The read below comes before the lock (2026-10-27, bergdb 005-46),
     * which only guards the shared decrypting Salsa object: under it, a read waited for every
     * other read's I/O, and for what that one waited for, such as the writer's force.
     */
    public void read(long position, byte[] dest, int destOffset, int length) throws IOException {
        // Bergdb 019-02: array exceptions, after the inner read.
        Util.checkRange(dest, destOffset, length);
        long blockPos = (position / Salsa.BLOCK_SIZE) * Salsa.BLOCK_SIZE;
        long blockOffset = position % Salsa.BLOCK_SIZE;
        long lengthToRead = blockOffset + length;
        if (lengthToRead > Integer.MAX_VALUE) {
            throw new Error("lengthToRead is too large: " + lengthToRead + ".");
        }
        
        byte[] b = new byte[(int) lengthToRead];  // Should be fast stack allocation.
        stream.read(blockPos, b, 0, b.length);
        
        synchronized (readLock) {
            decrypt.setupBlockCounter(blockPos / Salsa.BLOCK_SIZE);
            decrypt.append(b, 0, b, 0, b.length);     // in-place decryption
        }
            
        assert length <= b.length;
        assert position >= blockPos;
            
        int diff = (int) (position - blockPos);
        System.arraycopy(b, diff, dest, destOffset, length);
    }

    /**
     * Encrypts and appends data to the stream: one append to the stream under this one, so a
     * FileStream that forces each append forces it once, as it does an append of the bytes
     * without encryption (2026-11-09, bergdb 020-24-07, U7-2); an append of more than
     * MAX_APPEND_BUFFER bytes goes in parts of that length. Until U7-2 it went in parts of
     * 100 kB, each a forced append of the FileStream: a flush of the database's write
     * buffer, up to 5 MB, made up to 50 forces, and puts with a crypto key were 6 to 8 times
     * slower than without it (on F53). The encrypted bytes are the same, as the keystream
     * depends only on the key and the stream position.
     */
    public void append(byte[] source, int sourceOffset, int length) throws IOException {
        // 150804 Frans: Memory management substantially improved.
        // No memory allocation in this method, but when an append is longer than the buffer:
        // it then grows, at least to twice its length, up to MAX_APPEND_BUFFER (U7-2).
        
        // Bergdb 019-02: a negative length returned, a long one threw an array exception.
        Util.checkRange(source, sourceOffset, length);
        if (length > appendBuffer.length && appendBuffer.length < MAX_APPEND_BUFFER) {
            long grown = Math.max(length, 2L * appendBuffer.length);
            appendBuffer = new byte[(int) Math.min(grown, MAX_APPEND_BUFFER)];
        }
        int remainingBytes = length;
        int offset = sourceOffset;
        
        while (remainingBytes > 0) {
            int chunkLength = remainingBytes > appendBuffer.length ? appendBuffer.length : remainingBytes;
            
            encrypt.append(source, offset, appendBuffer, 0, chunkLength);
            stream.append(appendBuffer, 0, chunkLength);
            
            offset += chunkLength;
            remainingBytes -= chunkLength;
        }
    }

    public void pretruncate(long position) throws IOException {
        stream.pretruncate(position);
    }

    public void close() throws IOException {
        stream.close();
    }
    
    // ======== Tests ========
    
    @Nano
    private static void test0() throws IOException {
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
    
    @Nano
    private static void test1() throws IOException {
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
    
    @Nano
    private static void testMultiAppend() throws IOException {
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
    
    @Nano
    private static void testReadPartOfBlock1() throws IOException {
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
    
    @Nano
    private static void testNon64a() throws IOException {
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
    
    @Nano
    private static void testNon64b() throws IOException {
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
    
    /**
     * Regression test for bergdb 005-45: getLength() gave the underlying stream's length when
     * this stream was made, and did not count the appends (after 150 bytes it said 0).
     */
    @Nano
    private static void testLengthCountsAppends() throws IOException {
        MemoryStream m = new MemoryStream();
        SalsaStream s = new SalsaStream(m, new byte[8], new byte[32]);
        Assert.assertEquals(0, s.getLength());
        s.append(new byte[100], 0, 100);
        s.append(new byte[50], 0, 50);
        Assert.assertEquals(150, s.getLength());
        
        s = new SalsaStream(m, new byte[8], new byte[32]);
        s.append(new byte[10], 0, 10);
        Assert.assertEquals(160, s.getLength());
    }
    
    /**
     * Regression test for bergdb 020-24-07, U7-2: an append is one append to the stream under
     * it, so a FileStream that forces each append forces it as often as it does the same
     * bytes appended to it directly. Until U7-2 an append went down in chunks of 100 kB, each
     * forced: a flush of the database's write buffer, up to 5 MB, made up to 50 forces, and
     * puts with a crypto key were 6 to 8 times slower than without (on F53). The encrypted
     * bytes are those of appends of any size, here of 777 bytes each: the keystream depends
     * only on the key and the stream position.
     */
    @Nano
    private static void testOneForcePerAppend(TestEnvironment env) throws IOException {
        Random r = new Random(7);
        byte[] nonce = new byte[8];
        r.nextBytes(nonce);
        byte[] key = new byte[32];
        r.nextBytes(key);
        byte[] data = new byte[450 * 1000];     // Past the first two files, of 200 kB.
        r.nextBytes(data);
        
        FileStream.ForceLogIo plainIo = new FileStream.ForceLogIo();
        FileStream plain = new FileStream(env.createTempDir(), plainIo, true);
        plain.append(data, 0, 1000);
        plain.append(data, 1000, data.length - 1000);
        int expected = plainIo.starting("APPEND").size();
        plain.close();
        
        FileStream.ForceLogIo io = new FileStream.ForceLogIo();
        FileStream file = new FileStream(env.createTempDir(), io, true);
        try {
            SalsaStream s = new SalsaStream(file, nonce, key);
            s.append(data, 0, 1000);
            s.append(data, 1000, data.length - 1000);
            Assert.assertEquals("the appends' forces", expected, io.starting("APPEND").size());
            
            MemoryStream m = new MemoryStream();
            SalsaStream small = new SalsaStream(m, nonce, key);
            for (int pos = 0; pos < data.length; pos += 777) {
                small.append(data, pos, Math.min(777, data.length - pos));
            }
            byte[] encrypted = new byte[data.length];
            file.read(0, encrypted, 0, encrypted.length);
            byte[] encryptedSmall = new byte[data.length];
            m.read(0, encryptedSmall, 0, encryptedSmall.length);
            Assert.assertArrayEquals("the encrypted bytes", encryptedSmall, encrypted);
            
            byte[] back = new byte[data.length];
            new SalsaStream(file, nonce, key).read(0, back, 0, back.length);
            Assert.assertArrayEquals("the bytes read back", data, back);
        } finally {
            file.close();
        }
    }
    
    @Nano
    private static void testNon64c() throws IOException {
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
