package bergdb.test;

import java.io.File;
import java.io.IOException;

import bergdb.nanotest.T;
import bergdb.nanotest.TestEnvironment;
import bergdb.storage.BufferedStream;
import bergdb.stream.FileStream;
import bergdb.stream.MemoryStream;

/**
 * Test performance related to file synchronization and BufferedStream.
 * 
 * @author Frans Lundberg
 */
public class FileSynchPerformance {
    
    @T("perf")
    public static void testRWS(TestEnvironment c) throws IOException, InterruptedException {
        run(c, "rws");
    }
    
    @T("perf")
    public static void testRWD(TestEnvironment c) throws IOException, InterruptedException {
        run(c, "rwd");
    }
    
    @T("perf")
    public static void testWait(TestEnvironment c) throws IOException, InterruptedException {
        // Tests whether consumer thread causes any significant CPU load when idle.
        // Suitable to start this test with "&" (in the background) and run
        //     top -p <PID>
        // in another terminal.
        //
        
        int[] times = { 100, 50, 20, 10 };
        Thread.sleep(10*1000);
        
        for (int i = 0; i < times.length; i++) {
            System.out.println("bufferTime: " + times[i]);
            MemoryStream s = new MemoryStream();
            BufferedStream buffered = new BufferedStream(s);
            System.out.println("  Sleeping...");
            Thread.sleep(20*1000);
            System.out.println("  Closing stream.");
            buffered.close();
            Thread.sleep(10*1000);
        }
    }
    
    public static void run(TestEnvironment c, String mode) throws IOException, InterruptedException {
        //final int bufferSize = 1*1000000;
        //final int bufferSize = 2*1000000;
        //final int bufferSize = 5*1000000;
        final int bufferSize = 10*1000000;
        //final int bufferSize = 20*1000000;
        //final int bufferSize = 50*1000000;
        
        //final int bufferTime = 20;   
        //final int bufferTime = 50;    
        final int bufferTime = 100;     
        //final int bufferTime = 200;   
        //final int bufferTime = 500;   
        
        FileStream s = new FileStream(new File("/f/bergdb-storage/test-FileSynchPerformance-" + mode));
        BufferedStream buffered = new BufferedStream(s, bufferSize, bufferTime);
        buffered.start();
        
        final int byteSize = 1000;
        byte[] bytes = new byte[byteSize];
        
        long t = System.nanoTime();
        final int n = 100*1000;
        
        for (int i = 0; i < n; i++) {
            buffered.append(bytes, 0, byteSize);
        }
        buffered.close();
        s.close();
        t = System.nanoTime() - t;
        
        c.report(mode + "-time", 1e-9*t);
        //c.report(mode + "-timePerWrite", 1e-9*t / n);
    }
}

/*

130322 Removed mode option from MultiFileStream. "rws" always used. Other modes not needed because
    of the bunch-up by BufferedStream.

130108 Results of testWait()

Code:

        int[] times = { 100, 50, 20, 10 };
        Thread.sleep(10*1000);
        for (int i = 0; i < times.length; i++) {
            System.out.println("bufferTime: " + times[i]);
            MemoryStream s = new MemoryStream();
            BufferedStream buffered = new BufferedStream(s);
            System.out.println("  Sleeping...");
            Thread.sleep(20*1000);
            System.out.println("  Closing stream.");
            buffered.flushAndClose();
            Thread.sleep(10*1000);
        }

Tests whether consumer thread causes any significant CPU load when idle.
Code started with "&" process (in the background) and [top -d 1 -p <PID>] run in another terminal.

Result:

    bufferTime  CPU time of process during 20 s sleep with active consumer thread.
    100         0.08
    50          0.08
    20          0.08
    10          0.07

Conclusion: no measurable CPU load for inactive buffer due to consumer thread when bufferTime is
>= 10 ms. 0.08 s / 20.0 s = 0.004 (0.4%). The measured CPU load could be because of other Java 
threads (garbage collection perhaps).
*/