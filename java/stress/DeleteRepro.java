package bergdb.core;

import bergdb.pub.util.SyncLevel;
import bergdb.stream.MemoryStream;

/**
 * Minimal reproduction, 2026-10-12: deleting a key that does not exist, when
 * the key is 7 bytes or longer (two key segments), breaks the next restart.
 * See docs/levels.md.
 *
 * Usage: java -cp bergdb.jar:. bergdb.core.DeleteRepro /k/1000
 */
public class DeleteRepro {
    public static void main(String[] args) {
        String delKey = args[0];
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(stream).clock(clock).start();
        clock.setTime(10);
        db.execute(db.trans().put("/a", "x").build());
        clock.setTime(20);
        db.execute(db.trans().delete(delKey).build());      // key does not exist
        clock.setTime(30);
        db.execute(db.trans().put("/b", "y").build());
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        stream = stream.copy();
        try {
            db = Db.builder().testSetup(stream).clock(clock).start();
            System.out.println("restart OK; /a=" + DbUtil.getString(db, "/a") + ", /b=" + DbUtil.getString(db, "/b"));
            clock.setTime(40);
            db.execute(db.trans().put("/c", "z").build());
            db.sync(SyncLevel.ORDINARY);
            db.stop();
            stream = stream.copy();
            db = Db.builder().testSetup(stream).clock(clock).start();
            System.out.println("second restart OK; /c=" + DbUtil.getString(db, "/c"));
        } catch (Throwable e) {
            System.out.println("FAILED: " + e);
        }
    }
}
