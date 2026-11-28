package bergdb.core;

import java.io.File;
import java.io.RandomAccessFile;

import bergdb.pub.util.SyncLevel;
import bergdb.stream.FileStream;
import bergdb.stream.FileStreamIo;

/**
 * Review probe (bergdb 033, the second review of the start, 2026-11-28): one start of the
 * file database in a directory, a sync and a close, through the Core API without created.txt;
 * for StartChain2's -Ddiff, which loads this class once with each of two builds of BergDB
 * and compares what the two starts leave. It uses only what both builds have.
 */
public class StartOnce {
    static class Io extends FileStreamIo {
        protected void forceFile(File file, RandomAccessFile handle) { }
        protected void forceDirectory(File directory) { }
    }

    /**
     * "started LENGTH", or "refused" and the exceptions' classes and messages, the cut
     * position P of a BadTailException first ("P=...").
     */
    public static String run(String dir, String time, String force) {
        FileStream stream = null;
        try {
            stream = new FileStream(new File(dir), new Io(), !"off".equals(force));
            CoreTestClock clock = new CoreTestClock();
            clock.setTime(Long.parseLong(time));
            Db db = Db.builder().testSetup(stream).clock(clock).start();
            db.sync(SyncLevel.ORDINARY);
            long length = db.getStreamLength();
            db.close();
            return "started " + length;
        } catch (Throwable e) {
            if (stream != null) { try { stream.close(); } catch (Throwable x) { } }
            StringBuilder b = new StringBuilder("refused ");
            for (Throwable t = e; t != null; t = t.getCause()) {
                if (t instanceof bergdb.storage.BadTailException) {
                    b.insert(8, "P=" + ((bergdb.storage.BadTailException) t).getCutPos() + " ");
                }
            }
            for (Throwable t = e; t != null; t = t.getCause()) {
                String m = String.valueOf(t.getMessage());
                b.append(t.getClass().getSimpleName()).append(": ").append(m, 0, Math.min(m.length(), 300)).append(" | ");
            }
            return b.toString();
        }
    }
}
