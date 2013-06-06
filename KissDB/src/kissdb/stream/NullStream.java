package kissdb.stream;

import java.io.IOException;

import kissdb.nanotest.Assert;
import kissdb.nanotest.T;

/**
 * Dummy AppendOnlyStream that sometimes is useful for testing.
 * Only stores the 10,000 first bytes in memory, the rest of the appended bytes are discarded.
 * Throws IOException if an attempt is made to read bytes beyond the stored data.
 * 
 * @author Frans Lundberg
 */
public class NullStream implements AppendOnlyStream {   
    private static final int bufferSize = 10*1000;
    private byte[] buffer;
    private long length;
    private long firstPos;
    
    /**
     * Creates new empty (stream size = 0) write-once stream.
     */
    public NullStream() {
        synchronized (this) {
            length = 0;
            firstPos = 0;
            buffer = new byte[bufferSize];
        }
    }
    
    public synchronized long getLength() {
        return length;
    }
    
    public synchronized long getFirstPos() {
        return firstPos;
    }

    public synchronized void append(byte[] source, int off, int len) 
            throws IOException {
        if (length < bufferSize) {
            len = length + len > bufferSize ? (int) (bufferSize - length) : len;
            System.arraycopy(source, off, buffer, (int) length, len);
        }
        length += len;
    }

    public synchronized void read(long position, byte[] dest, int destPos, int length) 
            throws IOException {
        if (position + length > bufferSize) {
            throw new IOException("Cannot read " + length + " bytes at position " + position + ".");
        }
        System.arraycopy(buffer, (int) position, dest, destPos, length);
    }

    public synchronized void pretruncate(long firstValidPos) throws IOException {
        if (firstValidPos < 0 || firstValidPos > length) {
            throw new IllegalArgumentException("bad value, " + firstValidPos);
        }
        
        if (firstValidPos < length) {
            this.firstPos = firstValidPos;
        }
    }
    
    public synchronized void seekFirstPos(long pos) throws IOException {
        long length = getLength();
        if (pos < length) {
            throw new IllegalStateException("pos = " + pos + ", length = " + length);
        }
        
        this.firstPos = pos;
        this.length = pos;
    }
    
    public synchronized void stop() {
        // empty
    }

    public synchronized void close() {
        stop();
    }
    
    
    @T
    public static void test1() {
        NullStream s = new NullStream();
        Assert.assertEquals(0, s.getLength());
    }
    
    @T
    public static void testRead1() throws IOException {
        // Reads in the beginning of the stream.
        NullStream s = new NullStream();
        byte[] data = new byte[100];
        data[0] = 12;
        s.append(data, 0, 100);
        Assert.assertEquals(12, s.buffer[0]);
        
        byte[] buffer = new byte[100];
        s.read(0, buffer, 0, buffer.length);
        Assert.assertEquals(12, buffer[0]);
    }
    
    @T
    public static void testRead2() throws IOException {
        // Reads in non-existant part of the stream.
        NullStream s = new NullStream();
        byte[] data = new byte[20000];
        data[0] = 12;
        s.append(data, 0, data.length);
        byte[] buffer = new byte[100];
        s.read(0, buffer, 0, buffer.length);
        Assert.assertEquals(12, buffer[0]);
        
        Exception ex = null;
        try {
            s.read(15000, buffer, 0, buffer.length);
        } catch (IOException e) {
            ex = e;
        }
        
        Assert.assertTrue(ex != null);
    }
    
    @T
    public static void testSize() throws IOException {
        NullStream s = new NullStream();
        Assert.assertEquals(0, s.getLength());
        s.append(new byte[100], 0, 100);
        Assert.assertEquals(100, s.getLength());
        
        s.pretruncate(50);
        Assert.assertEquals(100, s.getLength());
        Assert.assertEquals(50, s.getFirstPos());
    }
    
    public static void main(String[] args) throws IOException {
        testRead1();
    }
}
