package bergdb.core;

import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.nio.file.Files;
import java.util.Arrays;

/**
 * Runs many jobs of the cross harness in one JVM (bergdb 012-05): a JVM start costs about
 * a quarter of a second, and a set has hundreds of jobs. A job file has one job a line:
 *
 * <pre>
 *   run OUT ARGS...     bergdb.cross.Run with ARGS, its output to OUT
 *   dump OUT ARGS...    bergdb.cross.Dump with ARGS
 *   scan OUT PATH       StreamScan of PATH (run here through its package-level API)
 * </pre>
 *
 * Each job writes its exit status, as the single program would exit, to OUT.exit, and an
 * exception that leaves it to OUT.err (status 3). Words are separated by spaces; paths
 * must not hold any. C's side runs its tools one job at a time with the same arguments
 * (cross.sh).
 *
 * Usage: java -ea -cp CLASSES bergdb.core.Batch JOBFILE
 */
public final class Batch {
    public static void main(String[] args) throws IOException {
        BufferedReader r = new BufferedReader(new FileReader(args[0]));
        int jobs = 0, failed = 0;
        for (String line; (line = r.readLine()) != null; ) {
            line = line.trim();
            if (line.isEmpty() || line.startsWith("#")) continue;
            String[] w = line.split(" +");
            File outFile = new File(w[1]);
            String[] rest = Arrays.copyOfRange(w, 2, w.length);
            int status;
            long t0 = System.nanoTime();
            PrintStream out = new PrintStream(new BufferedOutputStream(
                    new FileOutputStream(outFile), 1 << 16), false, "UTF-8");
            try {
                switch (w[0]) {
                case "run": status = bergdb.cross.Run.main(rest, out); break;
                case "dump": status = bergdb.cross.Dump.main(rest, out); break;
                case "scan": status = scan(rest[0], out, outFile); break;
                default: throw new IllegalArgumentException("unknown job " + w[0]);
                }
            } catch (Throwable e) {
                StringWriter sw = new StringWriter();
                e.printStackTrace(new PrintWriter(sw));
                Files.write(new File(w[1] + ".err").toPath(), sw.toString().getBytes("UTF-8"));
                status = 3;
            }
            out.close();
            Files.write(new File(w[1] + ".exit").toPath(), (status + "\n").getBytes("UTF-8"));
            jobs++;
            if (status != 0) failed++;
            System.out.println("job " + w[0] + " " + (System.nanoTime() - t0) / 1000000 + " ms status "
                    + status + " " + w[1]);
        }
        r.close();
        System.out.println("batch " + args[0] + ": " + jobs + " jobs, " + failed
                + " with a status other than 0");
    }

    /** StreamScan.main's work, without its System.exit: 1 if the scan printed an error. */
    static int scan(String path, PrintStream out, File outFile) throws IOException {
        out.println("streamscan 1");
        StreamScan.View view = StreamScan.View.open(new File(path), out);
        StreamScan scan = new StreamScan(view, out);
        scan.run();
        view.close();
        out.flush();
        BufferedReader r = new BufferedReader(new FileReader(outFile), 1 << 16);
        try {
            for (String line; (line = r.readLine()) != null; ) {
                if (line.startsWith("error ")) return 1;
            }
        } finally {
            r.close();
        }
        return 0;
    }
}
