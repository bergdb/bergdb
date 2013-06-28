package kissdb.test;

import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;

import kissdb.nanotest.TestCollector;
import kissdb.nanotest.T;


/**
 * Tests performance appending a single byte to a RandomAccessFile opened in three different
 * modes: rw, rwd, rws.
 * 
 * @author Frans Lundberg
 */
public class OneByteToFile {
       
    @T("perf")
    public static void rw(TestCollector c) throws IOException {
        writeOneByteChunks(c, "rw");
    }
    
    @T("perf")
    public static void rwd(TestCollector c) throws IOException {
        writeOneByteChunks(c, "rwd");
    }
    
    @T("perf")
    public static void rws(TestCollector c) throws IOException {
        writeOneByteChunks(c, "rws");
    }
    
    private static void writeOneByteChunks(TestCollector c, String mode) throws IOException {
        File file = File.createTempFile("FileSystemPerformance", ".temp");
        file.deleteOnExit();
        
        final int n = 100;
        RandomAccessFile r = new RandomAccessFile(file, mode);
        
        long t = System.nanoTime();
        for (int i = 0; i < n; i++) {
            r.write(i);    // writes a single byte
        }
        t = System.nanoTime() - t;
        r.close();
        
        c.report("n", n);
        c.report("time", t*1e-9);
        c.report("timePerWrite", t*1e-9 / n);
    }
}

/*

---- 2013-01-08 ----
Tests on Rose. Three tests run separately since addOneByteRW may affect the other
tests if run before them.

rw.timePerWrite:  14e-6
rwd.timePerWrite: 37e-3
rws.timePerWrite: 37e-3

37 ms was a bit more than I expected. Well, it is an Hitachi ATA disk 5400 rpm, 160 GB.
One rotation in 11 ms. Wonder why we need three rotations to make a one-byte write?
File system is ext4 (standard for Ubuntu).

*/