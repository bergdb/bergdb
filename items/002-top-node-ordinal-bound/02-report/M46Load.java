package bergdb.core;

import java.nio.file.Files;
import java.nio.file.Paths;

import bergdb.stream.MemoryStream;

/**
 * Bergdb item 002 (M46): starts a database from a stream saved by M46Wide (save), with
 * whichever bergdb.jar is on the class path, and reads /hot. Uses no top node field, so it
 * runs against the int and the long build alike.
 *
 * Usage: java -ea -cp bergdb.jar:. bergdb.core.M46Load FILE
 */
public final class M46Load {
    public static void main(String[] args) throws Exception {
        byte[] b = Files.readAllBytes(Paths.get(args[0]));
        MemoryStream stream = new MemoryStream();
        stream.append(b, 0, b.length);
        try {
            Db db = Db.builder().testSetup(stream).clock(new CoreTestClock()).start();
            byte[] v = DbUtil.get(db, "/hot");
            System.out.println(args[0] + ": started; /hot = " + (v == null ? "null" : new String(v)));
            db.stop();
        } catch (Throwable e) {
            System.out.println(args[0] + ": refused: " + e);
        }
    }
}
