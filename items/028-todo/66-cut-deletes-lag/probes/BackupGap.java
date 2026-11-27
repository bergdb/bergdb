import bergdb.pub.*;
import bergdb.pub.util.*;
import java.io.File;
import java.nio.file.*;
import java.util.*;

/**
 * bergdb 028-66 (2026-11-27): as 028-62's BackupCopy, copies of a running file database's
 * stream files in the order of their names, the last one last, each started and checked;
 * but a listed file that a cut deleted before the copy reached it is skipped, not a reason
 * to take the copy again. Such a copy has a gap (files copied before the missing one) or
 * misses its first files. With option C, each copy must either start, hold the state after
 * some n ("/seq/last" = m and every "/v/j" the latest n <= m) and have no gap in its files
 * after its start, or be refused at its start with the message that the stream lacks bytes.
 * Prints BACKUP GAP OK. Kind: functional.
 *
 * Usage, from the repository's root, after java/build.sh:
 *   javac -d CLASSES -cp java/build/bergdb.jar PROBES/BackupGap.java
 *   java -ea -cp CLASSES:java/build/bergdb.jar BackupGap DIR COPIES
 * DIR must not exist; it and DIR-copy are removed at the end.
 */
public class BackupGap {
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
        int whole = 0, gapStarted = 0, frontStarted = 0, gapRefused = 0, frontRefused = 0;
        int attempts = 0;
        for (int i = 0; i < copies; i++) {
            attempts++;
            Thread.sleep(r.nextInt(300));
            File[] files = new File(dir).listFiles((d, nm) -> nm.endsWith(".bergdb"));
            Arrays.sort(files, Comparator.comparing(File::getName));
            File copy = new File(dir + "-copy");
            deleteDir(copy);
            copy.mkdirs();
            boolean front = false, gap = false, copied = false;
            for (File f : files) {
                try {
                    Files.copy(f.toPath(), new File(copy, f.getName()).toPath());
                    copied = true;
                } catch (NoSuchFileException e) {
                    if (copied) gap = true; else front = true;
                }
            }
            if (!copied) { i--; continue; }
            Database db2;
            try {
                db2 = Factory.database().open(copy.getPath()).start();
            } catch (DbException e) {
                String m = String.valueOf(e.getMessage());
                if (!(gap || front) || !m.contains("lacks bytes")) {
                    System.out.println("BACKUP GAP FAILED: copy " + i + " gap " + gap + " front "
                            + front + ": " + e);
                    System.exit(1);
                }
                if (gap) gapRefused++; else frontRefused++;
                continue;
            }
            Connection c2 = db2.connection();
            String last = c2.get("/seq/last", String.class);
            long m = last == null ? 0 : Long.parseLong(last);
            for (int j = 0; j < 1000; j++) {
                long n = m - (((m - j) % 1000) + 1000) % 1000;
                String v = c2.get("/v/" + j, String.class);
                if (n >= 1) {
                    if (v == null || !v.startsWith(n + " ")) {
                        System.out.println("BACKUP GAP FAILED: copy " + i + " m " + m + " /v/" + j);
                        System.exit(1);
                    }
                } else if (v != null) {
                    System.out.println("BACKUP GAP FAILED: copy " + i + " /v/" + j + " at m " + m);
                    System.exit(1);
                }
            }
            db2.close();
            if (hasGap(copy)) {
                System.out.println("BACKUP GAP FAILED: copy " + i + " kept a gap after its start");
                System.exit(1);
            }
            if (gap) gapStarted++; else if (front) frontStarted++; else whole++;
        }
        stop = true;
        writer.join();
        db.close();
        deleteDir(new File(dir + "-copy"));
        deleteDir(new File(dir));
        System.out.println("copies " + copies + ": whole " + whole + "; with a gap, started "
                + gapStarted + ", refused " + gapRefused + "; without their first files, started "
                + frontStarted + ", refused " + frontRefused);
        System.out.println("BACKUP GAP OK");
    }

    static boolean hasGap(File d) {
        File[] fs = d.listFiles((x, nm) -> nm.endsWith(".bergdb"));
        Arrays.sort(fs, Comparator.comparing(File::getName));
        for (int i = 1; i < fs.length; i++) {
            long end = Long.parseLong(fs[i - 1].getName().substring(0, 14)) * 100000 + fs[i - 1].length();
            if (Long.parseLong(fs[i].getName().substring(0, 14)) * 100000 > end) return true;
        }
        return false;
    }

    static void deleteDir(File d) {
        File[] fs = d.listFiles();
        if (fs != null) for (File f : fs) f.delete();
        d.delete();
    }
}
