import java.io.*;
import java.util.*;

/**
 * ZeroTailProbe (031-02, F1). Without BergDB: does a kill of a process that appends to a
 * file with RandomAccessFile.write(), and forces each append as BergDB's FileStream does,
 * leave zeros within the file's length? A child appends chunks of 64 kB to 2 MB of the byte
 * 0x55 and forces each; the parent kills it (destroyForcibly) after 30 to 600 ms and counts
 * the files whose content is not all 0x55.
 *
 * Usage: java ZeroTailProbe parent DIR TRIALS [noforce]
 */
public class ZeroTailProbe {
    public static void main(String[] args) throws Exception {
        if (args[0].equals("child")) {
            boolean force = !args[2].equals("noforce");
            Random r = new Random(System.nanoTime());
            try (RandomAccessFile f = new RandomAccessFile(args[1], "rw")) {
                while (true) {
                    byte[] b = new byte[65536 + r.nextInt(2_000_000)];
                    Arrays.fill(b, (byte) 0x55);
                    f.seek(f.length());
                    f.write(b);
                    if (force) f.getChannel().force(true);
                    if (f.length() > 200_000_000) f.setLength(0);
                }
            }
        }
        String dir = args[1];
        int trials = Integer.parseInt(args[2]);
        String mode = args.length > 3 ? args[3] : "force";
        new File(dir).mkdirs();
        String java = ProcessHandle.current().info().command().orElse("java");
        Random r = new Random(1);
        int bad = 0;
        for (int t = 0; t < trials; t++) {
            File file = new File(dir, "f.bin");
            file.delete();
            Process p = new ProcessBuilder(java, "-cp", System.getProperty("java.class.path"), "ZeroTailProbe", "child",
                    file.getPath(), mode).redirectErrorStream(true).start();
            Thread.sleep(300 + r.nextInt(600));
            p.destroyForcibly();
            p.waitFor();
            long n = file.length();
            long firstZero = -1;
            try (BufferedInputStream in = new BufferedInputStream(new FileInputStream(file), 1 << 20)) {
                for (long i = 0; i < n; i++) {
                    int c = in.read();
                    if (c != 0x55) { firstZero = i; break; }
                }
            }
            if (firstZero >= 0) {
                bad++;
                System.out.println("trial " + t + ": length " + n + ", not 0x55 from " + firstZero + " (" + (n - firstZero)
                        + " bytes)");
            }
        }
        System.out.println("trials " + trials + ", files with a zeroed tail " + bad);
    }
}
