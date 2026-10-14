package bergdb.test.manual;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;

import bergdb.nanotest.CommandLine;

/**
 * Executable class that tests bulk sequential read from a file.
 * 
 * @author Frans Lundberg
 */
public class DiskReadSpeed {
    private String filename;
    private int mb;
    
    void go(String[] args) throws IOException, InterruptedException {
        CommandLine line = new CommandLine(args);
        
        if (line.has("help")) {
            printHelp();
            return;
        }
        
        handleOptions(line);
        
        if (line.has("create")) {
            create();
        } else {
            runReadTest();
        }
    }
    
    private void create() throws IOException {
        File file = new File(filename);
        byte[] buffer = new byte[1000000];
        
        FileOutputStream out = new FileOutputStream(file);
        try {
            for (int i = 0; i < mb; i++) {
                out.write(buffer, 0, buffer.length);
            }
        } finally {
            out.close();
        }
    }

    /**
     * Runs test and reports directly to System.out.
     */
    private void runReadTest() throws IOException, InterruptedException {
        File file = new File(filename);
        byte[] buffer = new byte[1*1000000];
        
        long t0 = System.nanoTime();
        double elapsed;
        long totalBytesRead = 0;
        
        FileInputStream in = new FileInputStream(file);
        try {
            while (true) {
                int readBytes = in.read(buffer, 0, buffer.length);
                if (readBytes == -1) {
                    break;
                }
                
                totalBytesRead += readBytes;
            }
        } finally {
            in.close();
        }
        
        elapsed = 1e-9 * (System.nanoTime() - t0);
        double mb = totalBytesRead * 1e-6;
        double mbPerSec = mb / elapsed;
        
        System.out.format("%.1f MB in %.1f s, %.1f MB/s.\n", mb, elapsed, mbPerSec);
    }
    
    private void handleOptions(CommandLine line) {
        filename = "DiskReadSpeed.dat";
        if (line.hasOne("file")) {
            filename = line.getOne("file");
        }
        
        mb = 100;
        if (line.hasOne("mb")) {
            mb = Integer.parseInt(line.getOne("mb"));
        }
    }

    private void printHelp() {
        StringBuilder b = new StringBuilder();
        b.append("Tool to test sequential read speed of the file system.\n");
        b.append("Create (-create) a test file, then read it while timing performance.\n");
        b.append("\n");
        b.append("Options (all are optional):\n");
        b.append("  -help\n");
        b.append("    Prints help.\n");
        b.append("  -file <filename>\n");
        b.append("    Name of file to read from. Default: 'DiskReadSpeed.dat'.\n");
        b.append("  -create [<filename>]);\n");
        b.append("    Create a test file with the given filename (or use default filename).\n");
        b.append("  -mb <sizeInMB>\n");
        b.append("    Size of file to create with -create.\n");
        b.append("\n");
        b.append("On Linux, drop system cache with:\n");
        b.append("  sudo bash -c \"echo 3 > /proc/sys/vm/drop_caches\"\n");
        b.append("On Linux, print memory usage with:\n");
        b.append("  free -m\n");
        
        System.out.println(b.toString());
    }

    public static void main(String[] args) throws Exception {
        new DiskReadSpeed().go(args);
    }
}
