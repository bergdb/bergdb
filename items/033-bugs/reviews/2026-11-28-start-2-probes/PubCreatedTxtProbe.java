package bergdb.core;

import java.io.File;
import java.nio.file.Files;
import java.util.Arrays;

import bergdb.pub.Database;
import bergdb.pub.Factory;

/**
 * Review probe (bergdb 033, the second review of the start, 2026-11-28): created.txt and the
 * stream through the Pub API (Factory.database().create(DIR) and open(DIR)), for the review's
 * F1 and F3.
 *
 * F1: a database is created in a directory, a value put and synced, and the database
 * closed; its directory then has created.txt and one stream file. The stream file's bytes are
 * made zeros, with its length kept, or cut to its first 100 bytes, and the database started
 * with create() and with open(): the probe prints what the start says.
 *
 * F3: two databases, A and B, each with a value. created.txt of A is made empty (as a kill
 * between the file's making and its write leaves it), and A started and closed: the probe
 * prints whether created.txt was written again. Then B's stream files are put in the place of
 * A's, and A's directory started: with the empty created.txt, and, the control, with A's own.
 *
 * Usage, from java/ after build.sh:
 *   javac -d CLASSES -cp build/bergdb.jar PROBES/PubCreatedTxtProbe.java
 *   java -ea -cp CLASSES:build/bergdb.jar bergdb.core.PubCreatedTxtProbe OUT
 */
public class PubCreatedTxtProbe {
    public static void main(String[] args) throws Exception {
        File base = new File(args[0]);
        File a = new File(base, "a"), b = new File(base, "b");
        rm(base);
        make(a, "of a");
        make(b, "of b");
        File stream = new File(a, "00000000000000.bergdb");
        byte[] bytes = Files.readAllBytes(stream.toPath());
        byte[] txt = Files.readAllBytes(new File(a, "created.txt").toPath());
        System.out.println("a database with one value: created.txt of " + txt.length + " bytes, the stream file "
                + bytes.length + " bytes, the files " + Arrays.toString(a.list()));

        System.out.println("F1:");
        for (String what : new String[] {"zeros", "its first 100 bytes"}) {
            for (String how : new String[] {"create", "open"}) {
                Files.write(stream.toPath(), what.equals("zeros") ? new byte[bytes.length] : Arrays.copyOf(bytes, 100));
                System.out.println("  created.txt there, the stream file " + what + ", " + how + "(): " + start(a, how));
            }
        }
        Files.write(stream.toPath(), bytes);

        System.out.println("F3:");
        File aTxt = new File(a, "created.txt");
        Files.write(aTxt.toPath(), new byte[0]);
        System.out.println("  created.txt empty, the database's own stream, open(): " + start(a, "open")
                + "; created.txt after it: " + aTxt.length() + " bytes");
        Files.write(stream.toPath(), Files.readAllBytes(new File(b, "00000000000000.bergdb").toPath()));
        System.out.println("  created.txt empty, the other database's stream file in the stream file's place, open(): "
                + start(a, "open") + "; created.txt after it: " + aTxt.length() + " bytes");
        Files.write(aTxt.toPath(), txt);
        Files.write(stream.toPath(), Files.readAllBytes(new File(b, "00000000000000.bergdb").toPath()));
        System.out.println("  the control, created.txt whole, the other database's stream file, open(): "
                + start(a, "open"));
        rm(base);
    }

    static void make(File dir, String value) {
        try (Database db = Factory.database().create(dir.getPath()).start()) {
            db.connection().put("/k/note.txt", value);
            db.sync();
        }
    }

    static String start(File dir, String how) {
        try (Database db = how.equals("create") ? Factory.database().create(dir.getPath()).start()
                : Factory.database().open(dir.getPath()).start()) {
            return "started, /k/note.txt reads " + db.connection().get("/k/note.txt", String.class);
        } catch (Throwable e) {
            String m = String.valueOf(e.getMessage());
            return e.getClass().getSimpleName() + ": " + m.substring(0, Math.min(m.length(), 420));
        }
    }

    static void rm(File f) {
        File[] c = f.listFiles();
        if (c != null) for (File x : c) rm(x);
        f.delete();
    }
}
