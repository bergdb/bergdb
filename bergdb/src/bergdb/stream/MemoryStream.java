package bergdb.stream;

import java.io.EOFException;
import java.io.IOException;
import java.util.ArrayList;

import bergdb.common.Bug;
import bergdb.common.Util;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;

/**
 * An in-memory implementation of AppendOnlyStream. Useful for testing.
 * Allocates memory in 1 MB chunks.
 * 
 * @author Frans Lundberg
 */
public class MemoryStream implements AppendOnlyStream {
    //
    // Synch note: no effort is made to allow truly concurrent readers. This class is for testing
    // only and reads/appends will be very fast anyway. Therefore all methods are synchronized.
    //
    
    private long streamLength;
    private static final int ARRAY_SIZE = Util.identity(1 * 1000000);
    private int firstArrayIndex;    // NOTE Consider: mayby a long?
    private ArrayList<byte[]> arrays;
    private long firstValidPos;
    private boolean closed = false;
    private boolean appendHasBeenCalled = false;
    
    /**
     * Creates new empty (stream size = 0) write-once stream.
     */
    public MemoryStream() {
        synchronized (this) {
            streamLength = 0;
            firstArrayIndex = 0;
            arrays = new ArrayList<byte[]>();
            firstValidPos = 0;
        }
    }
    
    /**
     * Copies the data in the stream. AppendListener is *not* copied. The fields 
     * 'closed', 'appendHasBeenCalled' are not copied.
     */
    public synchronized MemoryStream copy() {
        MemoryStream copy = new MemoryStream();
        copy.streamLength = this.streamLength;
        copy.firstValidPos = this.firstValidPos;
        copy.firstArrayIndex = this.firstArrayIndex;
        
        copy.arrays = new ArrayList<byte[]>(this.arrays.size());
        for (int i = 0; i < this.arrays.size(); i++) {
            byte[] array = this.arrays.get(i);
            assert array != null;
            byte[] arrayCopy = new byte[array.length];
            System.arraycopy(array, 0, arrayCopy, 0, array.length);
            copy.arrays.add(arrayCopy);
        }
        
        assert copy.arrays.size() == this.arrays.size() 
                : copy.arrays.size() + " != " + this.arrays.size();
        assert copy.assertOk();
        
        return copy;
    }
    
    /**
     * @throws AssertionError if state not ok.
     */
    public synchronized boolean assertOk() {
        // Note, more tests could be useful.
        
        long lastArrayIndex = firstArrayIndex + arrays.size() - 1;
        long expected = streamLength / ARRAY_SIZE;
        if (lastArrayIndex != expected) {
            throw new AssertionError("lastArrayIndex = " + lastArrayIndex 
                    + ", arrays.size()=" + arrays.size() + ", expected = " + expected
                    + ", streamLength = " + streamLength + ", firstArrayIndex = " + firstArrayIndex);
        }
        
        return true;
    }
    
    public synchronized final long getLength() {
        return streamLength;
    }
    
    public synchronized final long getFirstPos() {
        return firstValidPos;
    }
    
    public synchronized int getFirstArrayIndex() {
        return firstArrayIndex;
    }

    public synchronized void append(byte[] source, int off, int len) 
            throws IOException {
        this.appendHasBeenCalled = true;
        
        if (closed) {
            throw new IOException("Cannot append to closed stream.");
        }
        
        long first = streamLength;
        long last = streamLength + len - 1;
        int firstArray = (int) (first / ARRAY_SIZE);     // index to first array
        int lastArray = (int) (last / ARRAY_SIZE);       // index to last array
        
        if (len > 0 && off > source.length - 1) {
            throw new IllegalArgumentException("bad off, " + off 
                    + ", source.length = " + source.length);
        }
        if (len > source.length - off) {
            throw new IllegalArgumentException("bad len, " + len + ", off = " 
                    + off + ", source.length = " + source.length);
        }
        
        if (firstArray < firstArrayIndex) {
            throw new Bug("firstArray=" + firstArray + ", firstArrayIndex=" + firstArrayIndex);
        }
        
        for (int i = firstArray; i <= lastArray; i++) {
            byte[] array;
            int firstInArray;
            int lastInArray;
            int length;
            
            if (arrays.size() < (i + 1) - firstArrayIndex) {
                arrays.add(new byte[ARRAY_SIZE]);
            }
            if (arrays.size() < (i + 1) - firstArrayIndex) {
                throw new Bug("Should not happen, arrays.size()=" + arrays.size() 
                        + ", firstArray=" + firstArray + ", lastArray=" + lastArray
                        + ", first=" + first + ", last=" + last + ", off=" + off + ", len=" + len);
            }
            
            firstInArray = (int) ((i == firstArray) ? 
                    streamLength % ARRAY_SIZE : 0);
            lastInArray =  (int) ((i == lastArray)  ?
                    last % ARRAY_SIZE : ARRAY_SIZE - 1);
            length = lastInArray - firstInArray + 1;
            array = getArray(i, -1);
            System.arraycopy(source, off, array, firstInArray, length);
            off += length;
            streamLength += length;
        }
    }

    public synchronized void read(long position, byte[] dest, int off, int len) 
            throws IOException {
        long size = getLength();
        long first = position;
        long last = position + len - 1;
        int destOffset = off;
        int firstArray = (int) (first / ARRAY_SIZE);
        int lastArray = (int) (last / ARRAY_SIZE);
        
        if (position < 0) {
            throw new IllegalArgumentException("Negative position not allowed, " 
                    + position + ".");
        }
        
        if (len == 0) {
            return;
        }
        
        if (position < firstValidPos) {
            throw new IOException("Cannot read from position " + position 
                    + ", first valid position is " + firstValidPos + ".");
        }
        
        if (position + len > size) {
            throw new EOFException("Not enough bytes left in the stream, " +
                    "position is " + position +", length to read is " + 
                    len + " and stream size is " + getLength() + ".");
        }
        
        for (int i = firstArray; i <= lastArray; i++) {
            byte[] array;
            int firstInArray;
            int lastInArray;
            int length;
            
            firstInArray = (int) ((i == firstArray) ? 
                    position % ARRAY_SIZE : 0);
            lastInArray =  (int) ((i == lastArray)  ?
                    last % ARRAY_SIZE : ARRAY_SIZE - 1);
            length = lastInArray - firstInArray + 1;
            
            array = getArray(i, position);
            System.arraycopy(array, firstInArray, dest, destOffset, length);
            destOffset += length;
        }
    }
    
    /**
     * 
     * @param index
     * @param pos   Only for exception error messages.
     * @return
     * @throws IOException
     */
    private byte[] getArray(int index, long pos) throws IOException {
        int i = index - firstArrayIndex;
        if (i < 0) {
            throw new IOException("Cannot read memory stream at block index " + index 
                    + ". firstArrayIndex=" + firstArrayIndex + ", trying to read position " + pos + ".");
        }
        if (i > arrays.size() - 1) {
            throw new IOException("Cannot read memory stream at block index " + index 
                    + "; stream not that large. firstArrayIndex=" + firstArrayIndex 
                    + ", arrays.size()=" + arrays.size() + ", trying to read position " + pos + ".");
        }
        
        return arrays.get(index - firstArrayIndex);
    }
    
    public synchronized void pretruncate(long spos) {
        if (spos < 0) {
            throw new IllegalArgumentException("Bad spos, cannot be neg, was " + spos + ".");
        }
        
        int index = (int) (spos / ARRAY_SIZE);
        
        if (index > this.firstArrayIndex) {
            int diff = index - firstArrayIndex;
            for (int i = 0; i < diff; i++) {
                arrays.remove(0);
            }
            firstArrayIndex = firstArrayIndex + diff;
        }
        
        firstValidPos = firstArrayIndex * ARRAY_SIZE;
        //this.firstValidPos = spos;   // <-- code before 130326
    }
    
    public synchronized void seekFirstPos(long pos) {
        if (appendHasBeenCalled) {
            throw new IllegalStateException("Cannot call seekTo() after append() has been called.");
        }
        
        long length = getLength();
        if (length > pos) {
            throw new IllegalStateException("pos > getLength, pos = " + pos + ", length = " + length);
        }
        
        if (pos % ARRAY_SIZE != 0) {
            throw new IllegalArgumentException("pos = " + pos + ", cannot seek to that pos, pos % "
                    + ARRAY_SIZE + " != 0.");
        }
        
        streamLength = pos;
        if (pos / ARRAY_SIZE > Integer.MAX_VALUE) {
            throw new Bug("Unexpected, ARRAY_SIZE = " + ARRAY_SIZE + ", pos = " + pos + ".");
        }
        firstArrayIndex = (int) (pos / ARRAY_SIZE);
        arrays = new ArrayList<byte[]>();
        firstValidPos = pos;
    }
    
    /**
     * Truncates the stream to a specific size by removing data from the end of the stream. 
     * Useful for stream crash testing.
     * 
     * @param newLength Stream length after truncation.
     */
    public synchronized void truncate(long newLength) {
        long currentLength = getLength();
        
        if (newLength > currentLength) {
            throw new IllegalArgumentException("newLength larger than " +
                    "current length, " + newLength + " > " + currentLength + ".");
        }
        
        if (newLength == currentLength) {
            return;
        }
        
        this.streamLength = newLength;
        int lastArrayIndex = (int) ((streamLength / ARRAY_SIZE) - firstArrayIndex);
        
        while (true) {
            int arrayCount = arrays.size();
            if (arrayCount > lastArrayIndex + 1) {
                arrays.remove(arrayCount - 1);
            } else {
                break;
            }
        }
        
        assert assertOk();
    }    

    public synchronized void stop() {
        this.closed = true;
    }

    public synchronized void close() {
        stop();
    }
    
    public static class Tester {
        public Tester() {}
        
        @T
        public static void testSize1() throws IOException {
            MemoryStream s = new MemoryStream();
            
            s.append(new byte[0], 0, 0);
            s.append(new byte[123], 0, 123);
            Assert.assertEquals("size", 123L, s.getLength());
        }
        
        @T
        public static void testOneByte() throws IOException {
            MemoryStream s = new MemoryStream();
            byte[] dest = new byte[1024];
            s.append(new byte[]{1}, 0, 1);
            s.read(0, dest, 0, 1);
            Assert.assertEquals("size", 1L, s.getLength());
            Assert.assertEquals("first byte", (byte) 1, dest[0]);
        }
        
        @T
        public static void testSize2() throws IOException {
            MemoryStream s = new MemoryStream();
            byte[] bytes = new byte[1024 * 1024 + 1];
            for (int i : bytes) {
                bytes[i] = 1;
            }
            s.append(bytes, 0, bytes.length);
            Assert.assertEquals("size", (long) bytes.length, s.getLength());
            s.append(bytes, 0, bytes.length);
            
            Assert.assertEquals("size appended", bytes.length * 2L, s.getLength());
        }
        
        @T
        public static void testArrays() throws IOException {
            MemoryStream s = new MemoryStream();
            byte[] bytes = new byte[1024 * 1024 + 1];
            for (int i = 0; i < bytes.length; i++) {
                bytes[i] = 1;
            }
            s.append(bytes, 0, bytes.length);
            for (int i = 0; i < bytes.length; i++) {
                bytes[i] = 2;
            }
            s.append(bytes, 0, bytes.length);
            
            byte[] dest = new byte[10];
            s.read(1000, dest, 0, dest.length);
            Assert.assertEquals("byte0", (byte) 1, dest[0]);
            Assert.assertEquals("byte7", (byte) 1, dest[7]);
            s.read(1024*1024, dest, 0, 10);
            Assert.assertEquals("byte0", (byte) 1, dest[0]);
            Assert.assertEquals("byte1", (byte) 2, dest[1]);
        }
        
        @T
        public static void testTruncate1() throws IOException {
            MemoryStream s = new MemoryStream();
            byte[] bytes = Util.getTestBytes(1024 * 1024);
            
            s.append(bytes, 0, bytes.length);
            s.append(bytes, 0, bytes.length);
            
            s.truncate(1024 * 1024 + 38);
            Assert.assertEquals("size", 1024 * 1024 + 38L, s.getLength());
            
            s.truncate(123456);
            Assert.assertEquals("size2", 123456L, s.getLength());
        }
        
        @T
        public static void testTruncate2() throws IOException {
            MemoryStream s = new MemoryStream();
            byte[] bytes = Util.getTestBytes(1000000 + 123);
            
            s.append(bytes, 0, bytes.length);
            
            s.truncate(1000000 + 64);
            Assert.assertEquals("size", 1000000 + 64, s.getLength());
            
            byte[] buffer = new byte[100];
            s.read(0, buffer, 0, buffer.length);
            Assert.assertEquals(bytes[0], buffer[0]);
            Assert.assertEquals(bytes[92], buffer[92]);
            
            s.read(1000000 + 64 - 100, buffer, 0, buffer.length);
            Assert.assertEquals(bytes[1000064 - 100], buffer[0]);
            Assert.assertEquals(bytes[1000064 - 10], buffer[90]);
        }
        
        @T
        public static void testPretruncate1() throws IOException {
            MemoryStream s = new MemoryStream();
            byte[] bytes = Util.getTestBytes(MemoryStream.ARRAY_SIZE);
            
            Assert.assertEquals(0, s.firstArrayIndex);
            
            s.append(bytes, 0, bytes.length);
            s.append(bytes, 0, bytes.length);
            s.append(bytes, 0, bytes.length);
            
            s.pretruncate(1 * MemoryStream.ARRAY_SIZE);
            Assert.assertEquals(1, s.firstArrayIndex);
            
            s.pretruncate(1 * MemoryStream.ARRAY_SIZE);
            Assert.assertEquals(1, s.firstArrayIndex);
            
            s.pretruncate(1 * MemoryStream.ARRAY_SIZE + 1);
            Assert.assertEquals(1, s.firstArrayIndex);
            
            s.pretruncate(0);
            Assert.assertEquals(1, s.firstArrayIndex);
        }
        
        @T
        public static void testPretruncate2() throws IOException {
            MemoryStream s = new MemoryStream();
            byte[] bytes = Util.getTestBytes(MemoryStream.ARRAY_SIZE);
            
            Assert.assertEquals(0, s.firstArrayIndex);
            
            s.append(bytes, 0, bytes.length);
            s.append(bytes, 0, bytes.length);
            s.append(bytes, 0, bytes.length);
            
            s.pretruncate(1 * MemoryStream.ARRAY_SIZE - 1);
            Assert.assertEquals(0, s.firstArrayIndex);
            
            s.pretruncate(1 * MemoryStream.ARRAY_SIZE);
            Assert.assertEquals(1, s.firstArrayIndex);
            
            s.pretruncate(1 * MemoryStream.ARRAY_SIZE + 1);
            Assert.assertEquals(1, s.firstArrayIndex);
            
            s.pretruncate(2 * MemoryStream.ARRAY_SIZE - 1);
            Assert.assertEquals(1, s.firstArrayIndex);
            
            s.pretruncate(2 * MemoryStream.ARRAY_SIZE);
            Assert.assertEquals(2, s.firstArrayIndex);
            
            s.pretruncate(2 * MemoryStream.ARRAY_SIZE + 1);
            Assert.assertEquals(2, s.firstArrayIndex);
        }
    }
    
    public static void main(String[] args) throws Exception {
        MemoryStream.Tester.testPretruncate1();
    }
}
