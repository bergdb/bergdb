package bergdb.core;

import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.lang.management.ManagementFactory;
import java.lang.reflect.Method;

import bergdb.stream.FileStreamIo;

/**
 * A FileStreamIo that times the disk's slow operations for test reports (2026-10-27, bergdb
 * 005-46): the file forces, the directory forces (of new files and of cuts) and the deletes,
 * each with the five longest and the JVM uptime at their end. A wait of BergDB for the disk
 * does not count against item 009's pause target, but a report notes it (Frans,
 * 2026-10-27), and sets a long get or commit beside it. With writeBufferWaits(), the
 * writer's waits for room in the write buffer.
 */
public class TimedIo extends FileStreamIo {
    final Times forces = new Times("file forces");
    final Times directoryForces = new Times("directory forces");
    final Times deletes = new Times("deletes");

    protected void forceFile(File file, RandomAccessFile handle) throws IOException {
        long t0 = System.nanoTime();
        try {
            super.forceFile(file, handle);
        } finally {
            forces.add(System.nanoTime() - t0);
        }
    }

    protected void forceDirectory(File directory) throws IOException {
        long t0 = System.nanoTime();
        try {
            super.forceDirectory(directory);
        } finally {
            directoryForces.add(System.nanoTime() - t0);
        }
    }

    protected boolean delete(File file) throws IOException {
        long t0 = System.nanoTime();
        try {
            return super.delete(file);
        } finally {
            deletes.add(System.nanoTime() - t0);
        }
    }

    /** Three lines, one for each kind, since the last call; the counts start again. */
    public String take() {
        return forces.take() + "\n" + directoryForces.take() + "\n" + deletes.take();
    }

    /**
     * The writer's waits for room in the write buffer since the last call, by reflection, so
     * that a tool also runs on a jar from before 005-46.
     */
    public static String writeBufferWaits(Db db) {
        try {
            Object in = db.getClass().getMethod("internal").invoke(db);
            Method m = in.getClass().getMethod("takeWriteBufferWaits");
            return String.valueOf(m.invoke(in));
        } catch (Exception e) {
            return "(no figures of the write buffer's waits in this jar)";
        }
    }

    /** Count, total, and the five longest with their uptimes. */
    static final class Times {
        final String name;
        long count, totalNanos;
        final long[] longest = new long[5];
        final long[] uptime = new long[5];

        Times(String name) {
            this.name = name;
        }

        synchronized void add(long nanos) {
            count++;
            totalNanos += nanos;
            for (int i = 0; i < longest.length; i++) {
                if (nanos > longest[i]) {
                    System.arraycopy(longest, i, longest, i + 1, longest.length - i - 1);
                    System.arraycopy(uptime, i, uptime, i + 1, uptime.length - i - 1);
                    longest[i] = nanos;
                    uptime[i] = ManagementFactory.getRuntimeMXBean().getUptime();
                    break;
                }
            }
        }

        synchronized String take() {
            StringBuilder sb = new StringBuilder(String.format("%s %d, %.1f ms in all", name,
                    count, totalNanos / 1e6));
            if (count > 0) {
                sb.append("; longest at uptime");
                for (int i = 0; i < longest.length && longest[i] > 0; i++) {
                    sb.append(String.format(" %.3fs (%.1f ms)", uptime[i] / 1e3, longest[i] / 1e6));
                }
            }
            count = 0;
            totalNanos = 0;
            java.util.Arrays.fill(longest, 0);
            java.util.Arrays.fill(uptime, 0);
            return sb.toString();
        }
    }
}
