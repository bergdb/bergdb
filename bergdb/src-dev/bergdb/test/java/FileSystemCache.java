package bergdb.test.java;

import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.MappedByteBuffer;
import java.nio.channels.FileChannel.MapMode;

import bergdb.nanotest.T;
import bergdb.nanotest.TestEnvironment;


/**
 * Tests performance of file system cache. How fast is it to read parts of 
 * a file that is in the OS cache already?
 * 
 * @author Frans Lundberg
 */
public class FileSystemCache {

    @T("perf")
    public static void run(TestEnvironment c) throws Exception {
        int[] blockSizes = new int[]{1, 1024, 2*1024, 4*1024, 8*1024};
        
        for (int i = 0; i < blockSizes.length; i++) {
            testBlockSize1(c, blockSizes[i]);
            testBlockSize2(c, blockSizes[i]);
            c.out().println("");
        }
    }
    
    private static void testBlockSize1(TestEnvironment c, int blockSize) throws IOException {
        File file = File.createTempFile(FileSystemCache.class.getName(), ".temp");
        file.deleteOnExit();
        RandomAccessFile f = new RandomAccessFile(file, "rw");
        byte[] block = new byte[blockSize];
        byte[] bytes = new byte[10*1024*1024];
        long t0, t1;
        
        c.out().println("RandomAccessFile with block size " + blockSize);
        for (int i = 0; i < bytes.length; i++) {
            bytes[i] = (byte) i;
        }
        
        f.write(bytes);
        
        f.seek(20*block.length);
        for (int i = 0; i < 10; i++) {
            f.readFully(block, 0, block.length);
        }
        
        long N = 100000;
        t0 = System.nanoTime();
        for (int i = 0; i < N; i++) {
            f.seek(20*block.length);
            f.readFully(block, 0, block.length);
        }
        t1 = System.nanoTime();
        f.close();
        
        double time = 1e-9 * (t1 - t0);
        c.report("timePerBlock" + block.length, time/N);
        c.report("timePerByte" + block.length, time / (N*block.length));
    }
    
    private static void testBlockSize2(TestEnvironment c, int blockSize) throws IOException {
        File file = File.createTempFile(FileSystemCache.class.getName(), ".temp");
        file.deleteOnExit();
        RandomAccessFile f = new RandomAccessFile(file, "rw");
        MappedByteBuffer buffer = f.getChannel().map(MapMode.READ_WRITE, 0, 10*1024*1024);
        byte[] block = new byte[blockSize];
        byte[] bytes = new byte[10*1024*1024];
        long t0, t1;
        
        c.out().println("MappedByteBuffer with block size " + blockSize);
        for (int i = 0; i < bytes.length; i++) {
            bytes[i] = (byte) i;
        }        
        f.write(bytes);
        
        for (int i = 0; i < 10; i++) {
            buffer.position(20*block.length);
            buffer.get(block, 0, block.length);
        }
        
        long N = 100000;
        t0 = System.nanoTime();
        for (int i = 0; i < N; i++) {
            buffer.position(20*block.length);
            buffer.get(block, 0, block.length);
        }
        t1 = System.nanoTime();
        f.close();
        
        double time = 1e-9 * (t1 - t0);
        c.report("timePerBlock" + block.length, time/N);
        c.report("timePerByte" + block.length, time / (N*block.length));
    }
}

/*
080920

/Frans/
Tests on Acer Laptop Extensa 5220. Ubuntu 8.04.
Conclusions: 
Using MappedByteBuffer increases performance with a factor of 2-4. Significant!
But, I believe the buffering is done in-process, so we might have have double
cache. File data cached both by OS and by MappedByteBuffer implementation?
Not sure.

Some output...

$ java -server -cp source/ com.bergdb.perf.Starter
RandomAccessFile with block size 1
com.bergdb.perf.FileSystemCache.timePerBlock1 = 1.32E-6
com.bergdb.perf.FileSystemCache.timePerByte1 = 1.32E-6
MappedByteBuffer with block size 1
com.bergdb.perf.FileSystemCache.timePerBlock1 = 4.33E-7
com.bergdb.perf.FileSystemCache.timePerByte1 = 4.33E-7

RandomAccessFile with block size 1024
com.bergdb.perf.FileSystemCache.timePerBlock1024 = 1.56E-6
com.bergdb.perf.FileSystemCache.timePerByte1024 = 1.53E-9
MappedByteBuffer with block size 1024
com.bergdb.perf.FileSystemCache.timePerBlock1024 = 3.48E-7
com.bergdb.perf.FileSystemCache.timePerByte1024 = 3.39E-10

RandomAccessFile with block size 2048
com.bergdb.perf.FileSystemCache.timePerBlock2048 = 1.77E-6
com.bergdb.perf.FileSystemCache.timePerByte2048 = 8.65E-10
MappedByteBuffer with block size 2048
com.bergdb.perf.FileSystemCache.timePerBlock2048 = 4.55E-7
com.bergdb.perf.FileSystemCache.timePerByte2048 = 2.22E-10

RandomAccessFile with block size 4096
com.bergdb.perf.FileSystemCache.timePerBlock4096 = 2.29741178E-6
com.bergdb.perf.FileSystemCache.timePerByte4096 = 5.60E-10
MappedByteBuffer with block size 4096
com.bergdb.perf.FileSystemCache.timePerBlock4096 = 7.59E-7
com.bergdb.perf.FileSystemCache.timePerByte4096 = 1.85E-10

RandomAccessFile with block size 8192
com.bergdb.perf.FileSystemCache.timePerBlock8192 = 4.06E-6
com.bergdb.perf.FileSystemCache.timePerByte8192 = 4.96E-10
MappedByteBuffer with block size 8192
com.bergdb.perf.FileSystemCache.timePerBlock8192 = 1.35E-6
com.bergdb.perf.FileSystemCache.timePerByte8192 = 1.65E-10

*/