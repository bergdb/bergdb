package bergdb.stream;

import java.io.IOException;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * A dummy AppendOnlyStream that does not really store the actual stream bytes.
 * An instance of this class only stores the 10,000 first bytes in memory, 
 * the rest of the appended bytes are discarded. 
 * This is sometimes useful for testing.
 * Throws IOException if an attempt is made to read bytes beyond the stored data.
 * 
 * @author Frans Lundberg
 */
public class DummyStream implements AppendOnlyStream {   
    private static final int bufferSize = 10*1000;
    private final byte[] buffer;
    private long length;
    private long firstPos;
    
    /**
     * Creates new empty (stream size = 0) write-once stream.
     */
    public DummyStream() {
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
            throw new IOException("DummyStream, cannot read " + length 
                    + " bytes at position " + position + ".");
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
    
    public void seekFirstPos(long pos) throws IOException {
        throw new UnsupportedOperationException("seekFirstPos not implemented for DummyStream");
    }
    
    public synchronized void stop() {
        // empty
    }

    public synchronized void close() {
        stop();
    }
    
    // ======== Tests ========
    
    @Nano
    private static void test1() {
        DummyStream s = new DummyStream();
        Assert.assertEquals(0, s.getLength());
    }
    
    @Nano
    private static void testRead1() throws IOException {
        // Reads in the beginning of the stream.
        DummyStream s = new DummyStream();
        byte[] data = new byte[100];
        data[0] = 12;
        s.append(data, 0, 100);
        Assert.assertEquals(12, s.buffer[0]);
        
        byte[] buffer = new byte[100];
        s.read(0, buffer, 0, buffer.length);
        Assert.assertEquals(12, buffer[0]);
    }
    
    @Nano
    private static void testRead2() throws IOException {
        // Reads in non-existant part of the stream.
        DummyStream s = new DummyStream();
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
    
    @Nano
    private static void testSize() throws IOException {
        DummyStream s = new DummyStream();
        Assert.assertEquals(0, s.getLength());
        s.append(new byte[100], 0, 100);
        Assert.assertEquals(100, s.getLength());
        
        s.pretruncate(50);
        Assert.assertEquals(100, s.getLength());
        Assert.assertEquals(50, s.getFirstPos());
    }
}
