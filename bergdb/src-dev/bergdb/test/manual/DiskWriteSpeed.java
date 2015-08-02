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
    private int testMb;
    private boolean delete;
    
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
        byte[] buffer = new byte[1*1000000];
        
        callSyncIfAppropriate();
        
        long t0 = System.nanoTime();
        double elapsed;
        long bytesWritten = 0;
        
        FileOutputStream out = new FileOutputStream(file);
        try {
            while (true) {
                out.write(buffer, 0, buffer.length);
                elapsed = 1e-9 * (System.nanoTime() - t0);
                bytesWritten += buffer.length;
                
                if (useMb()) {
                    if (bytesWritten >= testMb * 1000000L) {
                        break;
                    }
                } else {
                    if (elapsed > testTime) {
                        break;
                    }
                }
            }
        } finally {
            out.close();
        }
        
        callSyncIfAppropriate();
        
        elapsed = 1e-9 * (System.nanoTime() - t0);
        double mb = bytesWritten * 1e-6;
        double mbPerSec = mb / elapsed;
        
        System.out.format("%.1f MB in %.1f s, %.1f MB/s.\n", mb, elapsed, mbPerSec);
        
        if (delete) {
            file.delete();
        }
    }
    
    private boolean useMb() {
        return testMb != 0;
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
        
        testMb = 0;
        if (line.hasOne("mb")) {
            testMb = Integer.parseInt(line.getOne("mb"));
        }
        
        delete = true;
        if (line.hasOne("delete")) {
            if (line.getOne("delete").equals("false")) {
                delete = false;
            }
        }
        
        System.out.println("Options used:");
        
        if (testMb == 0) {
            System.out.println("  test time: " + testTime + "s.");
        } else {
            System.out.println("  mb: " + testMb);
        }
        
        System.out.println("  use sync: " + useSync);
        System.out.println("  test file: " + filename);
        System.out.println("  delete: " + delete);
    }

    private void printHelp() {
        System.out.println("Options:\n");
        System.out.println("  -time  Number of seconds to write data.");
        System.out.println("  -mb    MB of data to write (use one of 'time' and 'mb').");
        System.out.println("  -sync  true/false, use / don't use sync system command.");
        System.out.println("  -file  Name of file to create when writing.");
        System.out.println("  -delete true/false, to delete file when done, default is true.");
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

/*

150802 Frans:
Speed, Samsung 16 Pro SD card (class 10, microSDHC UHS-I Card, read speed up to 90 MB/s, 
write speed up to 50 MB/s).
  $ j bergdb.test.manual.DiskWriteSpeed -mb 1000 -file /media/f/9016-4EF8/t3.dat -delete false
  -->
  1000.0 MB in 88.7 s, 11.3 MB/s
11 MB/s is much lower than what Samsung brags about. Built-in card reader in cissi used (and Ubuntu).

*/