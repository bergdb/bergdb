package bergdb.stream;

import java.io.IOException;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * Decorator for a wrapped AppendOnlyStream; throws exception
 * if append() or pretruncate() is called. Otherwise, method invocations
 * are simply forwarded to the wrapped stream.
 * 
 * @author Frans Lundberg
 */
public final class ReadOnlyStream implements AppendOnlyStream {
    private final AppendOnlyStream stream;
    
    /**
     * Creates a new instance by wrapping the provided stream.
     */
    public ReadOnlyStream(AppendOnlyStream stream) {
        if (stream == null) {
            throw new IllegalArgumentException("stream == null not allowed");
        }
        this.stream = stream;
    }

    public long getLength() {
        return stream.getLength();
    }

    public long getFirstPos() {
        return stream.getFirstPos();
    }

    public void read(long position, byte[] dest, int destOffset, int length) throws IOException {
        stream.read(position, dest, destOffset, length);
    }

    /**
     * @throws ReadOnlyException Always.
     */
    public void append(byte[] source, int sourceOffset, int length) throws IOException {
        throw new ReadOnlyException("Cannot append to ReadOnlyStream.");
    }

    /**
     * @throws ReadOnlyException Always.
     */
    public void pretruncate(long position) throws IOException {
        throw new ReadOnlyException("Cannot do pretruncate on ReadOnlyStream.");
    }

    public void seekFirstPos(long position) throws IOException {
        stream.seekFirstPos(position);
    }

    public void close() throws IOException {
        stream.close();
    }
    
    public static class ReadOnlyException extends IOException {
        private static final long serialVersionUID = 1L;

        public ReadOnlyException(String message) {
            super(message);
        }
    }
    
    
    // ======== Test ========
    
    @Nano
    private static void testRead() throws IOException {
        MemoryStream m = new MemoryStream();
        byte[] bytes = new byte[]{1, 2, 3, 4};
        m.append(bytes, 0, bytes.length);
        
        ReadOnlyStream ro = new ReadOnlyStream(m);
        byte[] buffer = new byte[2];
        ro.read(1, buffer, 0, 2);
        
        Assert.assertEquals(2, buffer[0]);
        Assert.assertEquals(3, buffer[1]);
    }
    
    @Nano
    private static void testAppend() throws IOException {
        ReadOnlyStream ro = new ReadOnlyStream(new MemoryStream());
        ReadOnlyException ex = null;
        
        try {
            ro.append(new byte[1], 0, 1);
        } catch (ReadOnlyException e) {
            ex = e;
        }
        
        Assert.assertTrue(ex != null);
    }
}
