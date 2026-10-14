package bergdb.common;

import java.io.IOException;
import java.io.OutputStream;

import bergdb.nanotest.Assert;

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
    public void write(int b) {
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
    
    public long getByteCount() {
        return count;
    }
    
    // ======== Test ========
    
    public static void testCount() throws IOException {
        NullOutputStream out = new NullOutputStream();
        out.write(new byte[10]);
        out.write((byte) 12);
        out.write(new byte[20], 5, 2);
        out.close();
        Assert.assertEquals(10 + 1 + 5, out.getByteCount());
    }
} 
