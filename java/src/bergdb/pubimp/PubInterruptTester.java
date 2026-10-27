package bergdb.pubimp;

import java.io.File;
import java.nio.file.Files;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.util.Job;

/**
 * Interrupts and the Pub API (2026-10-27, bergdb 005-46); bergdb.core.InterruptTester has
 * the rest. A job's join() ends on an interrupt and returns the job's status, the flag set;
 * it threw a java.lang.Error ("Internal thread unexpectedly interrupted."). The builder's
 * dir() by an interrupted thread made a FileStream that threw ClosedByInterruptException.
 */
public class PubInterruptTester {
    private PubInterruptTester() {}

    @Nano
    public static void testDirAndJobJoinByInterruptedThread() throws Exception {
        File root = Files.createTempDirectory("bergdb-pub-interrupt-").toFile();
        Database db = null;
        try {
            Thread.currentThread().interrupt();
            try {
                db = Factory.database().dir(new File(root, "db").getPath()).start();
                Assert.assertTrue("the flag was lost", Thread.currentThread().isInterrupted());
            } finally {
                Thread.interrupted();
            }
            for (int i = 0; i < 100; i++) {
                db.connection().put("/p" + i, "value " + i);
            }
            Job job = db.addReplica("r", new File(root, "replica").getPath());
            Thread.currentThread().interrupt();
            try {
                Assert.assertTrue(job.join() != null);
                Assert.assertTrue("the flag was lost", Thread.currentThread().isInterrupted());
            } finally {
                Thread.interrupted();
            }
            job.join();
            Assert.assertEquals("value 7", db.connection().get("/p7", String.class));
        } finally {
            if (db != null) db.stop();
            Thread.sleep(200);
            remove(root);
        }
    }

    private static void remove(File f) {
        File[] fs = f.listFiles();
        if (fs != null) for (File c : fs) remove(c);
        f.delete();
    }
}
