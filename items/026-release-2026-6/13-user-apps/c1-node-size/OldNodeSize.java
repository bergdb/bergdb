import bergdb.core.Db;
import bergdb.storage.StreamFormatException;
import bergdb.stream.FileStream;

import java.io.File;
import java.nio.file.Files;
import java.security.MessageDigest;
import java.util.*;

/**
 * C1 of 026-13: a database that an earlier release made at the node size 62 (bergdb 026-08,
 * releases/next.md: "one that made a database at 8, 14 or 62 cannot start it with this
 * release, which refuses it, as before, with a StreamFormatException that writes nothing").
 * Starts it by the Core API three times; each start must throw StreamFormatException, and
 * every file of the directory must keep its bytes (names, sizes and SHA-256 compared).
 *
 * Usage: java -cp bergdb-release.jar:out OldNodeSize DIR
 */
public class OldNodeSize {
    public static void main(String[] a) throws Exception {
        File dir = new File(a[0]);
        Map<String, String> before = digest(dir);
        for (int i = 0; i < 3; i++) {
            try {
                Db db = Db.builder().mainStream(new FileStream(dir, false)).start();
                db.close();
                System.out.println("FAIL OldNodeSize: the start of a node-size-62 database was taken");
                System.exit(1);
            } catch (StreamFormatException e) {
                if (i == 0) Common.log("refused: " + e.getMessage());
            }
            Map<String, String> after = digest(dir);
            if (!after.equals(before)) {
                System.out.println("FAIL OldNodeSize: the refused start changed the files: " + before + " -> " + after);
                System.exit(1);
            }
        }
        Common.log("OK OldNodeSize: 3 starts refused with StreamFormatException, " + before.size() + " files unchanged");
    }

    static Map<String, String> digest(File dir) throws Exception {
        Map<String, String> m = new TreeMap<>();
        for (File f : Objects.requireNonNull(dir.listFiles())) {
            byte[] h = MessageDigest.getInstance("SHA-256").digest(Files.readAllBytes(f.toPath()));
            m.put(f.getName(), f.length() + ":" + HexFormat.of().formatHex(h, 0, 8));
        }
        return m;
    }
}
