package bergdb.stream;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.RandomAccessFile;

/**
 * A simple AppendOnlyStream stored in a single file.
 * Good for testing, but not useful for most real applications since 
 * the file grows indefinitely.
 * 
 * @author Frans Lundberg
 */
public class OneFileStream implements AppendOnlyStream {
    private RandomAccessFile rfile;
    private Object sizeSynch = new Object();
    private long size;
    
    /**
     * Creates a new append-only storage, or opens existing one.
     * The stream size is assumed to equal the file size.
     */
    public OneFileStream(File file) throws FileNotFoundException, IOException {
        rfile = new RandomAccessFile(file, "rw");
        size = rfile.length();
    }
    
    public long getLength() {
        synchronized (sizeSynch) {
            return size;
        }
    }
    
    /**
     * Always returns 0, file never pretruncated.
     */
    public long getFirstPos() {
        return 0;
    }

    public void append(byte[] source, int sourceOffset, int length) throws IOException {   
        synchronized (rfile) {
            rfile.seek(rfile.length());
            rfile.write(source, sourceOffset, length);
            
            synchronized (sizeSynch) {
                size += length;
            }
        }
    }

    public void read(long position, byte[] dest, int destOffset, int length) throws IOException {
        synchronized (rfile) {
            rfile.seek(position);
            rfile.readFully(dest, destOffset, length);
        }
    }
    
    public void stop() {
        if (rfile != null) {
            try {
                rfile.close();
            } catch (IOException e) {
                // empty, nothing we can do
            }
        }
    }
    
    public void close() {
        stop();
    }

    /**
     * The method in this class does nothing. Disk space is never reclaimed.
     */
    public void pretruncate(long position) throws IOException {
        // Note. An alternative implementation could copy the file to shrink it.
        // This could be done by simply stopping the stream to copy the file, or better but more
        // advanced, the file could be copied while the DB is running and a switch-over to the 
        // new file and a delete of the old one is done.
    }
    
    public void seekFirstPos(long pos) {
        throw new UnsupportedOperationException();
    }
}
