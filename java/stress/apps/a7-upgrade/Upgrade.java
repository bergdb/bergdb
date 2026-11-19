import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;

import java.io.File;
import java.nio.file.Files;
import java.security.MessageDigest;
import java.util.*;

/**
 * App 7 of 024-26: a user upgrades from release 2026.4 to 2026.5. Run with each jar:
 *   java -cp bergdb-2026.4.jar:out Upgrade write DIR     makes a database with 2026.4
 *   java -cp bergdb-release.jar:out Upgrade open DIR     must refuse it, and change no file
 *   java -cp bergdb-2026.4.jar:out Upgrade check DIR     2026.4 still reads it all
 * Each prints OK or FAIL.
 */
public class Upgrade {
    public static void main(String[] a) throws Exception {
        String mode = a[0];
        File dir = new File(a[1]);
        if (mode.equals("write")) {
            Common.rmrf(dir);
            try (Database db = Factory.database().create(dir.getPath()).start()) {
                Connection c = db.connection();
                for (int i = 0; i < 2000; i++) c.put("/u/k" + i + ".txt", "v" + i);
                for (int i = 0; i < 2000; i += 3) c.delete("/u/k" + i + ".txt");
                c.sync();
            }
            System.out.println("OK written");
        } else if (mode.equals("open")) {
            String before = digest(dir);
            try (Database db = Factory.database().open(dir.getPath()).start()) {
                System.out.println("FAIL a database of 2026.4 was opened: " + db.connection().get("/u/k1.txt", String.class));
                System.exit(1);
            } catch (Exception e) {
                String after = digest(dir);
                System.out.println("refused: " + e.getClass().getName() + ": " + e.getMessage());
                if (!before.equals(after)) { System.out.println("FAIL the refused start changed the files"); System.exit(1); }
                if (!String.valueOf(e.getMessage()).contains("2026.4")) System.out.println("NOTE the message does not name 2026.4");
                System.out.println("OK refused, files unchanged");
            }
            // create() on it too: must refuse as well, and not make a new database over it.
            try (Database db = Factory.database().create(dir.getPath()).start()) {
                System.out.println("FAIL create() opened a database of 2026.4");
                System.exit(1);
            } catch (Exception e) {
                if (!before.equals(digest(dir))) { System.out.println("FAIL create() changed the files"); System.exit(1); }
                System.out.println("OK create() refused too: " + e.getClass().getSimpleName());
            }
        } else {
            try (Database db = Factory.database().open(dir.getPath()).start()) {
                Connection c = db.connection();
                for (int i = 0; i < 2000; i++) {
                    String v = c.get("/u/k" + i + ".txt", String.class);
                    String exp = i % 3 == 0 ? null : "v" + i;
                    if (!Objects.equals(v, exp)) { System.out.println("FAIL k" + i + " = " + v); System.exit(1); }
                }
            }
            System.out.println("OK 2026.4 reads it all");
        }
    }

    static String digest(File dir) throws Exception {
        MessageDigest md = MessageDigest.getInstance("SHA-256");
        File[] fs = dir.listFiles();
        Arrays.sort(fs);
        for (File f : fs) {
            md.update(f.getName().getBytes());
            if (f.isFile()) md.update(Files.readAllBytes(f.toPath()));
        }
        return HexFormat.of().formatHex(md.digest());
    }
}
