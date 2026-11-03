package bergdb.core;

import bergdb.stream.FileStream;
import bergdb.stream.FileStreamIo;
import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.ByteBuffer;
import java.nio.MappedByteBuffer;
import java.nio.channels.FileChannel;
import java.nio.channels.FileLock;
import java.nio.channels.ReadableByteChannel;
import java.nio.channels.WritableByteChannel;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

/** Delivers an interrupt immediately inside each interruptible I/O boundary. */
public final class IoInterruptProbe {
    static final class InterruptIo extends FileStreamIo {
        boolean interruptFile, interruptDirectory, interruptRead;
        final List<RandomAccessFile> writers = new ArrayList<>();
        final List<FileChannel> readers = new ArrayList<>();
        protected RandomAccessFile open(File f) throws IOException {
            RandomAccessFile out = super.open(f);
            writers.add(out);
            return out;
        }
        protected void forceFile(File f, RandomAccessFile out) throws IOException {
            if (interruptFile) {
                interruptFile = false;
                Thread.currentThread().interrupt();
            }
            super.forceFile(f, out);
        }
        protected void forceDirectory(File dir) throws IOException {
            if (interruptDirectory) {
                interruptDirectory = false;
                Thread.currentThread().interrupt();
            }
            super.forceDirectory(dir);
        }
        protected FileChannel openRead(File f) throws IOException {
            FileChannel ch = super.openRead(f);
            readers.add(ch);
            return new ReadBoundary(ch, this);
        }
    }

    static final class ReadBoundary extends FileChannel {
        final FileChannel ch;
        final InterruptIo io;
        ReadBoundary(FileChannel ch, InterruptIo io) { this.ch = ch; this.io = io; }
        public int read(ByteBuffer dst, long p) throws IOException {
            if (io.interruptRead) {
                io.interruptRead = false;
                Thread.currentThread().interrupt();
            }
            return ch.read(dst, p);
        }
        public int read(ByteBuffer dst) throws IOException { return ch.read(dst); }
        public long read(ByteBuffer[] dst, int off, int len) throws IOException { return ch.read(dst, off, len); }
        public int write(ByteBuffer src) throws IOException { return ch.write(src); }
        public long write(ByteBuffer[] src, int off, int len) throws IOException { return ch.write(src, off, len); }
        public int write(ByteBuffer src, long p) throws IOException { return ch.write(src, p); }
        public long position() throws IOException { return ch.position(); }
        public FileChannel position(long p) throws IOException { ch.position(p); return this; }
        public long size() throws IOException { return ch.size(); }
        public FileChannel truncate(long n) throws IOException { ch.truncate(n); return this; }
        public void force(boolean meta) throws IOException { ch.force(meta); }
        public long transferTo(long p, long n, WritableByteChannel dst) throws IOException { return ch.transferTo(p, n, dst); }
        public long transferFrom(ReadableByteChannel src, long p, long n) throws IOException { return ch.transferFrom(src, p, n); }
        public MappedByteBuffer map(MapMode mode, long p, long n) throws IOException { return ch.map(mode, p, n); }
        public FileLock lock(long p, long n, boolean shared) throws IOException { return ch.lock(p, n, shared); }
        public FileLock tryLock(long p, long n, boolean shared) throws IOException { return ch.tryLock(p, n, shared); }
        protected void implCloseChannel() throws IOException { ch.close(); }
    }

    static void requireFlag(String label) {
        if (!Thread.interrupted()) throw new AssertionError(label + " lost interrupt");
    }

    public static void main(String[] args) throws Exception {
        File dir = Files.createTempDirectory(new File(args[0]).toPath(), "io-interrupt-").toFile();
        InterruptIo io = new InterruptIo();
        FileStream stream = new FileStream(dir, io);
        try {
            stream.append(new byte[] {1}, 0, 1);
            io.interruptFile = true;
            stream.append(new byte[] {2, 3}, 0, 2);
            requireFlag("file force");
            byte[] bytes = new byte[3];
            stream.read(0, bytes, 0, 3);
            if (bytes[0] != 1 || bytes[1] != 2 || bytes[2] != 3) throw new AssertionError("bad forced bytes");
            System.out.println("Interrupt at file force: append completed, bytes correct, flag kept");

            io.interruptDirectory = true;
            stream.append(new byte[300_000], 0, 300_000);
            requireFlag("directory force");
            if (stream.getLength() != 300_003) throw new AssertionError("bad length");
            System.out.println("Interrupt at directory force during rotation: append completed, flag kept");

            io.interruptRead = true;
            stream.read(0, bytes, 0, 3);
            requireFlag("read");
            if (bytes[0] != 1 || bytes[1] != 2 || bytes[2] != 3) throw new AssertionError("bad read bytes");
            System.out.println("Interrupt at positional read: read completed, bytes correct, flag kept");
        } finally {
            Thread.interrupted();
            stream.close();
            for (RandomAccessFile f : io.writers) if (f.getFD().valid()) throw new AssertionError("writer leaked");
            for (FileChannel ch : io.readers) if (ch.isOpen()) throw new AssertionError("reader leaked");
            System.out.println("All original and reopened data handles closed");
            try (java.util.stream.Stream<java.nio.file.Path> paths = Files.walk(dir.toPath())) {
                for (java.nio.file.Path p : paths.sorted(Comparator.reverseOrder()).toList()) Files.delete(p);
            }
        }
    }
}
