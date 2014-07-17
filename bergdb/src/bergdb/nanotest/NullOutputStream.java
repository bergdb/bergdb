package bergdb.nanotest;

import java.io.IOException;
import java.io.OutputStream;

/**
 * Dummy output stream useful for testing.
 * Write methods and does nothing but counts the number of bytes 
 * "written" to the output stream.
 * 
 * @author Frans Lundberg
 */
public class NullOutputStream extends OutputStream {
    private long count = 0;
    
    /**
     * This method just adds one to the byte count.
     */
    public void write(int b) throws IOException {
        count++;
    }

    /**
     * This method just adds bytes.length to the byte count.
     */
    public void write(byte[] bytes) {
        count += bytes.length;
    }
    
    /**
     * This method justs add length to the byte count.
     */
    public void write(byte[] bytes, int length, int offset) {
        count += length;
    }
    
    /**
     * Returns the current byte count.
     */
    public long getByteCount() {
        return count;
    }
    
    /**
     * Does nothing.
     */
    public void stop() {
    }
}
