package bergdb.test.manual;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;

import bergdb.nanotest.CommandLine;

/**
 * Executable class that tests bulk sequential write to a single file.
 * 
 * @author Frans Lundberg
 */
public class DiskWriteSpeed {
    private double testTime;
    private boolean useSync;
    private String filename;
    
    void go(String[] args) throws IOException, InterruptedException {
        CommandLine line = new CommandLine(args);
        
        if (line.has("help")) {
            printHelp();
            return;
        }
        
        handleOptions(line);
        
        runTest();
    }
    
    /**
     * Runs test and reports directly to System.out.
     */
    private void runTest() throws IOException, InterruptedException {
        File file = new File(filename);
        file.deleteOnExit();
        
        byte[] buffer = new byte[1*1000000];
        
        callSyncIfAppropriate();
        
        long t0 = System.nanoTime();
        double elapsed;
        long size = 0;
        
        FileOutputStream out = new FileOutputStream(file);
        try {
            while (true) {
                out.write(buffer, 0, buffer.length);
                elapsed = 1e-9 * (System.nanoTime() - t0);
                size += buffer.length;
                
                if (elapsed > testTime) {
                    break;
                }
            }
        } finally {
            out.close();
        }
        
        callSyncIfAppropriate();
        
        testTime = (System.nanoTime() - t0) * 1e-9;
        double mb = size * 1e-6;
        double mbPerSec = mb / elapsed;
        
        System.out.format("%.1f MB in %.1f s, %.1f MB/s.\n", mb, testTime, mbPerSec);
        
        file.delete();
    }

    private void callSyncIfAppropriate() throws IOException, InterruptedException {
        if (useSync) {
            System.out.print("Calling sync... ");
            sync();
            System.out.println("done.");
        }
    }
    
    private void handleOptions(CommandLine line) {
        testTime = 15.0;
        if (line.hasOne("time")) {
            testTime = Double.parseDouble(line.getOne("time"));
        }
        
        useSync = false;
        if (line.hasOne("sync")) {
            if (line.getOne("sync").equals("true")) {
                useSync = true;
            }
        }
        
        filename = "DiskSpeed-test-file.dat";
        if (line.hasOne("file")) {
            filename = line.getOne("file");
        }
        
        System.out.println("Options used:");
        System.out.println("  test time: " + testTime + "s.");
        System.out.println("  use sync: " + useSync);
        System.out.println("  test file: " + filename);
    }

    private void printHelp() {
        System.out.println("Options:\n");
        System.out.println("  -time  Number of seconds to write data.");
        System.out.println("  -sync  true/false, use / don't use sync system command.");
        System.out.println("  -file  Name of file to create when writing.");
    }

    private void sync() throws IOException, InterruptedException {
        ProcessBuilder b = new ProcessBuilder();
        b.command("sync");
        b.redirectErrorStream(true);
        
        Process p = b.start();
        p.waitFor();
    }
    
    public static void main(String[] args) throws Exception {
        new DiskWriteSpeed().go(args);
    }
}
