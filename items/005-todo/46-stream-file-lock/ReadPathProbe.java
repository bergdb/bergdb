import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.ByteBuffer;
import java.nio.channels.ClosedChannelException;
import java.nio.channels.FileChannel;
import java.nio.file.StandardOpenOption;
import java.util.Random;
import java.util.concurrent.atomic.AtomicLong;

/**
 * Probe for bergdb 005-46: the read paths it could take, on the JDK and the file system alone
 * (no BergDB). A file is read as FileStream reads it today (one RandomAccessFile, seek and
 * readFully under the file's monitor, which the writer's append and force hold too) and by
 * positional reads (FileChannel.read(buffer, position), pread) on a channel of their own.
 *
 * Usage: java -cp . ReadPathProbe MODE DIR ..., with MODE one of
 *   force DIR SECONDS CHUNK
 *       A writer appends CHUNK bytes and forces the file (FileChannel.force(true), as
 *       FileStreamIo does), holding the file's monitor, as DbFile.append does, and waits 5 ms
 *       before the next append, as BufferedStream's consumer does before a flush.
 *       Reader "monitor" reads 100 bytes of the written part under the same monitor, through
 *       the writer's RandomAccessFile; reader "pread" through a channel of its own, no lock.
 *   cut DIR FILES FILE_MB
 *       FILES files of FILE_MB MB and one more; reader "pread" reads the last one while the
 *       others are deleted one by one, the directory forced after each, as FileStream's
 *       pretruncate does.
 *   interrupt DIR
 *       What an interrupt does to positional reads: a thread with its interrupt flag set
 *       reads, then another thread; then readers that clear the flag before a read and
 *       restore it after, and reopen the channel and read again when they find it closed,
 *       while a thread interrupts them every 100 microseconds.
 *   scale DIR FILE_MB SECONDS
 *       Random reads of 4 KB of a file in the OS's cache, with 1, 2, 4 and 8 threads:
 *       "monitor" (one RandomAccessFile, seek and readFully under its monitor, as today),
 *       "pread" (one FileChannel, positional reads) and "raf-each" (a RandomAccessFile per
 *       thread, as a pool of handles would give).
 * DIR must not exist or be empty; the probe deletes its files at the end.
 */
public class ReadPathProbe {
    public static void main(String[] args) throws Exception {
        String mode = args[0];
        File dir = new File(args[1]);
        dir.mkdirs();
        System.out.println("ReadPathProbe " + String.join(" ", args) + "; Java "
                + System.getProperty("java.version") + ", " + System.getProperty("os.name") + " "
                + System.getProperty("os.version"));
        try {
            if (mode.equals("force")) {
                force(dir, Integer.parseInt(args[2]), Integer.parseInt(args[3]));
            } else if (mode.equals("cut")) {
                cut(dir, Integer.parseInt(args[2]), Integer.parseInt(args[3]));
            } else if (mode.equals("interrupt")) {
                interrupt(dir);
            } else if (mode.equals("scale")) {
                scale(dir, Integer.parseInt(args[2]), Integer.parseInt(args[3]));
            } else {
                throw new IllegalArgumentException("unknown mode " + mode);
            }
        } finally {
            File[] fs = dir.listFiles();
            if (fs != null) for (File f : fs) f.delete();
            dir.delete();
        }
    }

    static void force(File dir, int seconds, int chunk) throws Exception {
        File file = new File(dir, "f");
        final RandomAccessFile w = new RandomAccessFile(file, "rw");
        byte[] data = new byte[chunk];
        new Random(1).nextBytes(data);
        w.write(new byte[1000 * 1000]);
        w.getChannel().force(true);
        final AtomicLong written = new AtomicLong(w.length());
        final FileChannel ch = FileChannel.open(file.toPath(), StandardOpenOption.READ);
        final Object monitor = w;
        final long[] durations = new long[2];

        Loop monitorReader = new Loop("monitor") {
            final Random r = new Random(3);
            final byte[] dest = new byte[100];
            void once() throws IOException {
                long pos = (long) (r.nextDouble() * (written.get() - 100));
                synchronized (monitor) {
                    w.seek(pos);
                    w.readFully(dest);
                }
            }
        };
        Loop preadReader = new Loop("pread") {
            final Random r = new Random(4);
            final ByteBuffer dest = ByteBuffer.allocate(100);
            void once() throws IOException {
                long pos = (long) (r.nextDouble() * (written.get() - 100));
                dest.clear();
                while (dest.hasRemaining()) {
                    if (ch.read(dest, pos + dest.position()) < 0) throw new IOException("EOF");
                }
            }
        };
        monitorReader.start();
        preadReader.start();
        Stat appends = new Stat(), forces = new Stat();
        long end = System.nanoTime() + seconds * 1000000000L;
        while (System.nanoTime() < end) {
            long t0 = System.nanoTime();
            synchronized (monitor) {
                w.seek(w.length());
                w.write(data);
                long t1 = System.nanoTime();
                w.getChannel().force(true);
                forces.add(System.nanoTime() - t1);
            }
            appends.add(System.nanoTime() - t0);
            written.set(w.length());
            Thread.sleep(5);        // As BufferedStream's consumer, which waits a quarter of
                                    // its buffer time, 5 ms, before each flush.
        }
        monitorReader.finish();
        preadReader.finish();
        System.out.println(appends.line("writer, append of " + chunk + " bytes (write and force)"));
        System.out.println(forces.line("  of it the force"));
        System.out.println(monitorReader.stat.line("reader monitor (today)"));
        System.out.println(preadReader.stat.line("reader pread"));
        ch.close();
        w.close();
    }

    static void cut(File dir, int files, int fileMb) throws Exception {
        byte[] mb = new byte[1000 * 1000];
        new Random(1).nextBytes(mb);
        File[] fs = new File[files + 1];
        for (int i = 0; i <= files; i++) {
            fs[i] = new File(dir, String.format("%05d", i));
            try (RandomAccessFile f = new RandomAccessFile(fs[i], "rw")) {
                for (int j = 0; j < fileMb; j++) f.write(mb);
                f.getChannel().force(true);
            }
        }
        forceDirectory(dir);
        final File live = fs[files];
        final FileChannel ch = FileChannel.open(live.toPath(), StandardOpenOption.READ);
        final long size = ch.size();
        Loop reader = new Loop("pread") {
            final Random r = new Random(4);
            final ByteBuffer dest = ByteBuffer.allocate(100);
            void once() throws IOException {
                long pos = (long) (r.nextDouble() * (size - 100));
                dest.clear();
                while (dest.hasRemaining()) {
                    if (ch.read(dest, pos + dest.position()) < 0) throw new IOException("EOF");
                }
            }
        };
        reader.start();
        Thread.sleep(300);
        Stat deletes = new Stat(), forces = new Stat();
        long t0 = System.nanoTime();
        for (int i = 0; i < files; i++) {
            long a = System.nanoTime();
            if (!fs[i].delete()) throw new IOException("could not delete " + fs[i]);
            long b = System.nanoTime();
            forceDirectory(dir);
            deletes.add(b - a);
            forces.add(System.nanoTime() - b);
        }
        long cutNs = System.nanoTime() - t0;
        Thread.sleep(300);
        reader.finish();
        System.out.println(String.format("deleted %d files of %d MB, each followed by a directory"
                + " force: %.3f ms", files, fileMb, cutNs / 1e6));
        System.out.println(deletes.line("  the deletes"));
        System.out.println(forces.line("  the directory forces"));
        System.out.println(reader.stat.line("reader pread, of the file not deleted"));
        ch.close();
    }

    static void forceDirectory(File dir) throws IOException {
        try (FileChannel c = FileChannel.open(dir.toPath(), StandardOpenOption.READ)) {
            c.force(true);
        }
    }

    static void interrupt(File dir) throws Exception {
        final File file = new File(dir, "f");
        try (RandomAccessFile f = new RandomAccessFile(file, "rw")) {
            f.write(new byte[1000 * 1000]);
        }
        final FileChannel ch = FileChannel.open(file.toPath(), StandardOpenOption.READ);
        Thread a = new Thread() {
            public void run() {
                interrupt();
                try {
                    ch.read(ByteBuffer.allocate(10), 1000);
                    System.out.println("a positional read by a thread whose interrupt flag is set: OK");
                } catch (Throwable e) {
                    System.out.println("a positional read by a thread whose interrupt flag is set threw " + e);
                }
            }
        };
        a.start();
        a.join();
        try {
            ch.read(ByteBuffer.allocate(10), 1000);
            System.out.println("then a positional read by another thread: OK");
        } catch (Throwable e) {
            System.out.println("then a positional read by another thread threw " + e
                    + "; the channel is open: " + ch.isOpen());
        }

        // A RandomAccessFile read is not interruptible.
        try (RandomAccessFile f = new RandomAccessFile(file, "r")) {
            Thread.currentThread().interrupt();
            f.seek(1000);
            f.readFully(new byte[10]);
            System.out.println("a RandomAccessFile read by a thread whose interrupt flag is set: OK,"
                    + " the flag still set: " + Thread.interrupted());
        }

        // The mitigation: clear the flag before a read and restore it after; when the channel
        // is found closed (an interrupt that came during the read), reopen and read again.
        final Retrying retrying = new Retrying(file);
        final int n = 4;
        final Loop[] readers = new Loop[n];
        final long[] flagRestored = new long[n], flagLost = new long[n];
        for (int i = 0; i < n; i++) {
            final int ii = i;
            readers[i] = new Loop("retrying-" + i) {
                final Random r = new Random(ii);
                final ByteBuffer dest = ByteBuffer.allocate(100);
                void once() throws IOException {
                    boolean before = Thread.currentThread().isInterrupted();
                    retrying.read(dest, (long) (r.nextDouble() * 999000));
                    boolean after = Thread.currentThread().isInterrupted();
                    if (before && after) flagRestored[ii]++;
                    if (before && !after) flagLost[ii]++;
                    Thread.interrupted();       // The loop's own business: start clean.
                }
            };
        }
        for (Loop l : readers) l.start();
        long end = System.nanoTime() + 2000000000L;
        long interrupts = 0;
        while (System.nanoTime() < end) {
            readers[(int) (interrupts % n)].interrupt();
            interrupts++;
            long until = System.nanoTime() + 100000;
            while (System.nanoTime() < until) Thread.onSpinWait();
        }
        long reads = 0, restored = 0, lost = 0;
        for (int i = 0; i < n; i++) {
            readers[i].finish();
            reads += readers[i].stat.count;
            restored += flagRestored[i];
            lost += flagLost[i];
        }
        System.out.println("retrying readers, " + n + " threads, 2 s, an interrupt every 100 us: "
                + reads + " reads, " + interrupts + " interrupts, the channel reopened "
                + retrying.reopens.get() + " times, reads that failed 0 (a failure ends the probe);"
                + " reads by an interrupted thread " + (restored + lost) + ", flag restored after "
                + restored + ", lost " + lost);
        retrying.close();
    }

    /** Positional reads that an interrupt does not fail, by the mitigation of 005-46. */
    static final class Retrying {
        final File file;
        volatile FileChannel ch;
        final AtomicLong reopens = new AtomicLong();

        Retrying(File file) throws IOException {
            this.file = file;
            this.ch = FileChannel.open(file.toPath(), StandardOpenOption.READ);
        }

        void read(ByteBuffer dest, long pos) throws IOException {
            boolean interrupted = Thread.interrupted();
            try {
                while (true) {
                    FileChannel c = ch;
                    try {
                        dest.clear();
                        while (dest.hasRemaining()) {
                            if (c.read(dest, pos + dest.position()) < 0) throw new IOException("EOF");
                        }
                        return;
                    } catch (ClosedChannelException e) {
                        if (Thread.interrupted()) interrupted = true;
                        reopen(c);
                    }
                }
            } finally {
                if (interrupted) Thread.currentThread().interrupt();
            }
        }

        synchronized void reopen(FileChannel closed) throws IOException {
            if (ch == closed) {
                ch = FileChannel.open(file.toPath(), StandardOpenOption.READ);
                reopens.incrementAndGet();
            }
        }

        void close() throws IOException {
            ch.close();
        }
    }

    static void scale(File dir, int fileMb, int seconds) throws Exception {
        final File file = new File(dir, "f");
        byte[] mb = new byte[1000 * 1000];
        new Random(1).nextBytes(mb);
        try (RandomAccessFile f = new RandomAccessFile(file, "rw")) {
            for (int j = 0; j < fileMb; j++) f.write(mb);
        }
        final long size = file.length();
        final RandomAccessFile shared = new RandomAccessFile(file, "r");
        final FileChannel ch = FileChannel.open(file.toPath(), StandardOpenOption.READ);
        // Warm the OS's cache.
        ByteBuffer warm = ByteBuffer.allocate(1 << 20);
        for (long p = 0; p < size; p += warm.capacity()) {
            warm.clear();
            ch.read(warm, p);
        }
        String[] kinds = {"monitor", "pread", "raf-each"};
        for (final String kind : kinds) {
            StringBuilder sb = new StringBuilder(String.format("%-9s", kind));
            for (int threads : new int[] {1, 2, 4, 8}) {
                Loop[] ls = new Loop[threads];
                for (int i = 0; i < threads; i++) {
                    final int ii = i;
                    ls[i] = new Loop(kind + "-" + i) {
                        final Random r = new Random(ii);
                        final byte[] dest = new byte[4096];
                        final ByteBuffer buf = ByteBuffer.wrap(dest);
                        RandomAccessFile own;
                        void once() throws IOException {
                            long pos = (long) (r.nextDouble() * (size - 4096));
                            if (kind.equals("monitor")) {
                                synchronized (shared) {
                                    shared.seek(pos);
                                    shared.readFully(dest);
                                }
                            } else if (kind.equals("pread")) {
                                buf.clear();
                                while (buf.hasRemaining()) ch.read(buf, pos + buf.position());
                            } else {
                                if (own == null) own = new RandomAccessFile(file, "r");
                                own.seek(pos);
                                own.readFully(dest);
                            }
                        }
                    };
                }
                for (Loop l : ls) l.start();
                Thread.sleep(seconds * 1000L);
                long reads = 0;
                for (Loop l : ls) {
                    l.finish();
                    reads += l.stat.count;
                }
                sb.append(String.format("  %d threads %,9d reads/s", threads, reads / seconds));
            }
            System.out.println(sb);
        }
        ch.close();
        shared.close();
    }

    /** Calls once() until finish(), each call timed. */
    abstract static class Loop extends Thread {
        final Stat stat = new Stat();
        volatile boolean stop = false;
        volatile Throwable failure = null;

        Loop(String name) {
            super(name);
        }

        abstract void once() throws IOException;

        public void run() {
            try {
                while (!stop) {
                    long t0 = System.nanoTime();
                    once();
                    stat.add(System.nanoTime() - t0);
                }
            } catch (Throwable e) {
                failure = e;
            }
        }

        void finish() throws Exception {
            stop = true;
            join();
            if (failure != null) throw new RuntimeException("thread " + getName() + " failed", failure);
        }
    }

    /** Count, mean and longest of durations, and how many took more than 1, 10 and 100 ms. */
    static final class Stat {
        long count, total, max, over1, over5, over10, over100;

        synchronized void add(long ns) {
            count++;
            total += ns;
            max = Math.max(max, ns);
            if (ns > 1000000) over1++;
            if (ns > 5000000) over5++;
            if (ns > 10000000) over10++;
            if (ns > 100000000) over100++;
        }

        synchronized String line(String name) {
            return String.format("%s: %d, mean %.4f ms, longest %.3f ms; over 1 ms %d, over 5 ms %d,"
                    + " over 10 ms %d, over 100 ms %d", name, count, count == 0 ? 0 : total / 1e6 / count, max / 1e6,
                    over1, over5, over10, over100);
        }
    }
}
