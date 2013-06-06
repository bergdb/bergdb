package kissdb.test.java;

import java.util.Random;
import java.util.zip.Adler32;
import java.util.zip.CRC32;
import java.util.zip.Checksum;

import kissdb.nanotest.TestCollector;
import kissdb.nanotest.T;

public class ChecksumPerf {

    public static class MyChecksum1 implements Checksum {
        private int value;
        
        public void update(int b) {
            value += b;
        }

        public void update(byte[] b, int off, int len) {
            for (int i = 0; i < len; i++) {
                value += (b[off + i] & 0xff);
            }
        }

        public long getValue() {
            return value;
        }

        public void reset() {
            value = 0;
        }
    }
    
    @T("perf")
    public static void run(TestCollector c) throws Exception {
        c.report("notes", "Tests checksums");
        Checksum[] checksums = new Checksum[]{
                new Adler32(), new CRC32(), new MyChecksum1(), new MyChecksum2()};
        
        for (int i = 0; i < checksums.length; i++) {
            test(c, checksums[i]);
        }
    }
    
    private static void test(TestCollector c, Checksum cs) {
        long t0;
        long bytesWritten;
        
        c.out().println("Testing " + cs.getClass().getName());
        
        Random random = new Random(0);
        random.setSeed(0);
        byte[] testData = new byte[200];
        random.nextBytes(testData);
        
        bytesWritten = 0;
        t0 = System.nanoTime();
        while (true) {
            for (int i = 0; i < 1000; i++) {
                cs.update(testData, 0, testData.length);
                bytesWritten += testData.length;
                cs.reset();
            }
            
            if (System.nanoTime() - t0 > 2e9) {
                break;
            }
        }
        double time = (System.nanoTime() - t0) * 1e-9;
        double timePerByte = time / bytesWritten;
        
        //c.report("time", time);
        c.report("timePerByte", timePerByte);
        c.report("MBPerSec", bytesWritten / (1000*1000) / time);
    }
}
