package kissdb.common;

import java.io.IOException;
import java.io.OutputStream;
import java.util.ArrayList;

/**
 * A faster version of ByteArrayOutputStream.
 * This implementation uses a number of byte[] buffers instead of one.
 * 
 * @author Frans Lundberg
 */
public class MemoryOutputStream extends OutputStream {
    private long size;      // current byte size of the stream
    private ArrayList<byte[]> buffers;
    private int BUFFER_SIZE = 16 * 1024;
    
    public MemoryOutputStream() {
        size = 0;
        buffers = new ArrayList<byte[]>(10);
    }
    
    private void addBuffersIfNeeded(long sizeToWrite) {
        while (size + sizeToWrite > buffers.size() * BUFFER_SIZE) {
            buffers.add(new byte[BUFFER_SIZE]);
        }
    }
    
    /**
     * Writes one byte. Very slow, avoid using this method if performance
     * is of interest.
     */
    public void write(int b) throws IOException {
        write(new byte[]{(byte) b}, 0, 1);
    }

    /**
     * This method has this implementation: 
     * <code>write(bytes, 0, bytes.length);</code>.
     */
    public void write(byte[] bytes) throws IOException {
        write(bytes, 0, bytes.length);
    }
    
    /**
     * This is the preferred write method to use.
     */
    public void write(byte[] bytes, int offset, int length) throws IOException {
        long last = size + length - 1;
        int firstBuffer = (int) (size / BUFFER_SIZE);
        int lastBuffer = (int) (last / BUFFER_SIZE);
        
        if (length < 1) {
            return;
        }
        
        if (offset > bytes.length - 1) {
            throw new IllegalArgumentException("bad off, " + offset 
                    + ", bytes.length = " + bytes.length);
        }
        if (length > bytes.length - offset) {
            throw new IllegalArgumentException("bad len, " + length + ", off = " 
                    + offset + ", bytes.length = " + bytes.length);
        }
        
        addBuffersIfNeeded(length);
        
        for (int i = firstBuffer; i <= lastBuffer; i++) {
            byte[] array;
            int firstInBuffer;
            int lastInBuffer;            
            
            firstInBuffer = (int) ((i == firstBuffer) ? 
                    size % BUFFER_SIZE : 0);
            lastInBuffer =  (int) ((i == lastBuffer)  ?
                    last % BUFFER_SIZE : BUFFER_SIZE - 1);
            length = lastInBuffer - firstInBuffer + 1;
            array = buffers.get(i);
            System.arraycopy(bytes, offset, array, firstInBuffer, length);
            offset += length;
            size += length;
        }
    }
    
    /**
     * Returns the current size of the stream (number of bytes written to 
     * it).
     */
    public long getSize() {
        return size;
    }
    
    /**
     * Returns the array in which data written data is stored.
     */
    public ArrayList<byte[]> getBuffers() {
        return buffers;
    }
    
    /**
     * Does nothing.
     */
    public void stop() throws IOException {
    }
}
