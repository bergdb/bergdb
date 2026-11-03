package bergdb.core;

import bergdb.stream.FileStream;
import java.io.File;
import java.lang.reflect.InvocationTargetException;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.Comparator;
import java.util.concurrent.TimeUnit;

/** One JVM only: an external Python process checks the actual POSIX lock. */
public final class LockLoaderProbe {
    private static String nativeLock(File dir) throws Exception {
        String code = "import fcntl,sys\n"
                + "with open(sys.argv[1], 'r+b') as f:\n"
                + " try:\n"
                + "  fcntl.lockf(f, fcntl.LOCK_EX|fcntl.LOCK_NB, 1, 1<<62)\n"
                + "  print('ACQUIRED')\n"
                + " except BlockingIOError:\n"
                + "  print('REFUSED')\n";
        Process p = new ProcessBuilder("/usr/bin/python3", "-c", code,
                new File(dir, "bergdb.lock").getPath()).redirectErrorStream(true).start();
        if (!p.waitFor(5, TimeUnit.SECONDS)) {
            p.destroyForcibly();
            throw new AssertionError("native lock check hung");
        }
        String result = new String(p.getInputStream().readAllBytes(), StandardCharsets.UTF_8).trim();
        if (p.exitValue() != 0) throw new AssertionError(result);
        return result;
    }

    public static void main(String[] args) throws Exception {
        File dir = Files.createTempDirectory(new File(args[0]).toPath(), "lock-loader-").toFile();
        URL jar = new File(args[1]).toURI().toURL();
        try (URLClassLoader other = new URLClassLoader(new URL[] {jar}, null)) {
            FileStream first = new FileStream(dir);
            try {
                first.append(new byte[] {1, 2, 3}, 0, 3);
                System.out.println("Before second loader: " + nativeLock(dir));
                Class<?> fs = Class.forName("bergdb.stream.FileStream", true, other);
                try {
                    Object second = fs.getConstructor(File.class).newInstance(dir);
                    fs.getMethod("close").invoke(second);
                    throw new AssertionError("second loader unexpectedly opened");
                } catch (InvocationTargetException e) {
                    System.out.println("Second loader: " + e.getCause().getClass().getName());
                }
                System.out.println("After rejected open, first still open: " + nativeLock(dir));
                first.append(new byte[] {4}, 0, 1);
                System.out.println("First still accepts appends: length=" + first.getLength());
            } finally {
                first.close();
            }
        } finally {
            try (java.util.stream.Stream<java.nio.file.Path> paths = Files.walk(dir.toPath())) {
                for (java.nio.file.Path p : paths.sorted(Comparator.reverseOrder()).toList()) {
                    Files.delete(p);
                }
            }
        }
    }
}
