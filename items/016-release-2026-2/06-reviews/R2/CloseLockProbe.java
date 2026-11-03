package bergdb.core;

import bergdb.stream.DirectoryInUseException;
import bergdb.stream.FileStream;
import bergdb.stream.FileStreamIo;
import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.Comparator;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicReference;

/** Latch-controlled close/open and native-process exclusion, with exactly one JVM. */
public final class CloseLockProbe {
    static final class GateIo extends FileStreamIo {
        volatile boolean gate;
        final CountDownLatch entered = new CountDownLatch(1), release = new CountDownLatch(1);
        protected void forceDirectory(File directory) throws IOException {
            if (gate) {
                entered.countDown();
                boolean interrupted = false;
                try {
                    for (;;) {
                        try {
                            if (!release.await(5, TimeUnit.SECONDS)) throw new IOException("gate timeout");
                            break;
                        } catch (InterruptedException e) { interrupted = true; }
                    }
                } finally {
                    if (interrupted) Thread.currentThread().interrupt();
                }
            }
            super.forceDirectory(directory);
        }
    }

    static void requireRefused(File dir, String label) throws Exception {
        try {
            new FileStream(dir).close();
            throw new AssertionError(label + ": second stream opened");
        } catch (DirectoryInUseException expected) {
            System.out.println(label + ": refused");
        }
    }

    public static void main(String[] args) throws Exception {
        File dir = Files.createTempDirectory(new File(args[0]).toPath(), "close-lock-").toFile();
        GateIo io = new GateIo();
        FileStream first = new FileStream(dir, io);
        Thread closer = null;
        Process holder = null;
        try {
            first.append(new byte[500_000], 0, 500_000);
            io.gate = true;
            first.pretruncate(200_000);
            if (!io.entered.await(5, TimeUnit.SECONDS)) throw new AssertionError("no cut gate");
            AtomicReference<Throwable> failed = new AtomicReference<>();
            CountDownLatch closing = new CountDownLatch(1);
            closer = new Thread(() -> {
                closing.countDown();
                try { first.close(); } catch (Throwable e) { failed.set(e); }
            }, "review-closer");
            closer.setDaemon(true);
            closer.start();
            if (!closing.await(5, TimeUnit.SECONDS)) throw new AssertionError("no closer");
            requireRefused(dir, "Open while a cut keeps close unfinished");
            io.release.countDown();
            closer.join(5000);
            if (closer.isAlive() || failed.get() != null) throw new AssertionError("close failed", failed.get());
            new FileStream(dir).close();
            System.out.println("Open after completed close: succeeded");

            String code = "import fcntl,sys\n"
                    + "with open(sys.argv[1], 'r+b') as f:\n"
                    + " fcntl.lockf(f, fcntl.LOCK_EX|fcntl.LOCK_NB, 1, 1<<62)\n"
                    + " print('HELD', flush=True)\n"
                    + " sys.stdin.buffer.read(1)\n";
            holder = new ProcessBuilder("/usr/bin/python3", "-c", code,
                    new File(dir, "bergdb.lock").getPath()).redirectErrorStream(true).start();
            java.io.BufferedReader output = new java.io.BufferedReader(
                    new java.io.InputStreamReader(holder.getInputStream(), StandardCharsets.UTF_8));
            String line = output.readLine();
            if (!"HELD".equals(line)) throw new AssertionError("native holder: " + line);
            requireRefused(dir, "Open while a native process holds the lock");
            holder.getOutputStream().close();
            if (!holder.waitFor(5, TimeUnit.SECONDS) || holder.exitValue() != 0) {
                throw new AssertionError("native holder failed");
            }
            new FileStream(dir).close();
            System.out.println("Open after native process releases: succeeded");
        } finally {
            io.release.countDown();
            if (holder != null && holder.isAlive()) {
                holder.destroyForcibly();
                holder.waitFor(5, TimeUnit.SECONDS);
            }
            if (closer != null) closer.join(5000);
            first.close();
            try (java.util.stream.Stream<java.nio.file.Path> paths = Files.walk(dir.toPath())) {
                for (java.nio.file.Path p : paths.sorted(Comparator.reverseOrder()).toList()) {
                    Files.delete(p);
                }
            }
        }
    }
}
