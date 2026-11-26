import bergdb.pub.*;
import bergdb.pub.util.*;
import java.io.File;
import java.nio.file.*;
import java.util.*;

/**
 * bergdb 028-62 (2026-11-26): copies of a running file database's stream files, in the order
 * of their names, the last one last, each started and checked; FileStream's Javadoc, "A
 * backup by a copy of the files". A writer commits n = 1, 2, ...: "/v/(n % 1000)" = "n pad"
 * (1.5 kB) and "/seq/last" = "n", with a retain duration of 1 s, so that reclaim cuts and
 * files are deleted during the copies. A copy in which a listed file is missing (a cut
 * deleted it first) is taken again. A copy is right if it starts and holds the state after
 * some n: "/seq/last" = m and every "/v/j" the latest n <= m. Prints BACKUP COPY OK.
 * Kind: functional. About 3 minutes and 1 GB of disk at most for 100 copies on F53.
 *
 * Usage, from the repository's root, after java/build.sh:
 *   javac -d CLASSES -cp java/build/bergdb.jar PROBES/BackupCopy.java
 *   java -ea -cp CLASSES:java/build/bergdb.jar BackupCopy DIR COPIES
 * DIR must not exist; it and DIR-copy are removed at the end.
 */
public class BackupCopy {
    static volatile boolean stop = false;
    static volatile long written = 0;

    public static void main(String[] a) throws Exception {
        String dir = a[0];
        int copies = Integer.parseInt(a[1]);
        Database db = Factory.database().create(dir).start();
        db.setRetainDuration(Duration.seconds(1));
        Thread writer = new Thread(() -> {
            Connection c = db.connection();
            StringBuilder sb = new StringBuilder();
            for (int i = 0; i < 1500; i++) sb.append((char) ('a' + i % 26));
            String pad = sb.toString();
            long n = 0;
            while (!stop) {
                n++;
                c.w().put("/v/" + (n % 1000), n + " " + pad).put("/seq/last", "" + n).execute();
                written = n;
            }
        });
        writer.start();
        Random r = new Random(1);
        int ok = 0, retaken = 0, filesMax = 0, cutsSeen = 0;
        long lastFirst = -1;
        for (int i = 0; i < copies; i++) {
            Thread.sleep(r.nextInt(300));
            File[] files = new File(dir).listFiles((d, nm) -> nm.endsWith(".bergdb"));
            Arrays.sort(files, Comparator.comparing(File::getName));
            filesMax = Math.max(filesMax, files.length);
            if (!files[0].getName().equals(lastFirst < 0 ? "" : String.format("%014d.bergdb", lastFirst))) cutsSeen++;
            lastFirst = Long.parseLong(files[0].getName().substring(0, 14));
            File copy = new File(dir + "-copy");
            deleteDir(copy);
            copy.mkdirs();
            boolean missing = false;
            for (File f : files) {
                try {
                    Files.copy(f.toPath(), new File(copy, f.getName()).toPath());
                } catch (NoSuchFileException e) {
                    missing = true;
                    break;
                }
            }
            if (missing) { retaken++; i--; continue; }
            Database db2 = Factory.database().open(copy.getPath()).start();
            Connection c2 = db2.connection();
            String last = c2.get("/seq/last", String.class);
            long m = last == null ? 0 : Long.parseLong(last);
            for (int j = 0; j < 1000; j++) {
                long n = m - (((m - j) % 1000) + 1000) % 1000;
                String v = c2.get("/v/" + j, String.class);
                if (n >= 1) {
                    if (v == null || !v.startsWith(n + " ")) {
                        System.out.println("BACKUP FAILED: copy " + i + " m " + m + " /v/" + j + ": "
                                + (v == null ? null : v.substring(0, Math.min(20, v.length()))));
                        System.exit(1);
                    }
                } else if (v != null) {
                    System.out.println("BACKUP FAILED: copy " + i + " /v/" + j + " present at m " + m);
                    System.exit(1);
                }
            }
            db2.close();
            ok++;
            if (i % 10 == 0) System.out.println("copy " + i + ": " + files.length + " files from "
                    + files[0].getName() + ", m " + m + " of " + written);
        }
        stop = true;
        writer.join();
        db.close();
        deleteDir(new File(dir + "-copy"));
        deleteDir(new File(dir));
        System.out.println("copies " + ok + " right, " + retaken + " taken again (a listed file deleted),"
                + " first file changed " + cutsSeen + " times, at most " + filesMax + " files");
        System.out.println("BACKUP COPY OK");
    }

    static void deleteDir(File d) {
        File[] fs = d.listFiles();
        if (fs != null) for (File f : fs) f.delete();
        d.delete();
    }
}
