package bergdb.core;

import java.io.File;
import java.lang.reflect.Field;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.concurrent.TimeUnit;
import bergdb.storage.BufferedStream;
import bergdb.stream.DirectoryInUseException;
import bergdb.stream.FileStream;

/** Hold the consumer monitor so stop and interrupt both precede its next action. */
public final class ConsumerStopInterruptProbe {
    public static void main(String[] args) throws Exception {
        Path root = Path.of(args[0]);
        Files.createDirectories(root);
        File dir = Files.createTempDirectory(root, "consumer-stop-").toFile();
        BufferedStream b = new BufferedStream(new FileStream(dir), 1024, 60000);
        b.start();
        try {
            Field f = BufferedStream.class.getDeclaredField("consumer");
            f.setAccessible(true);
            Thread consumer = (Thread) f.get(b);
            long end = System.nanoTime() + TimeUnit.SECONDS.toNanos(2);
            while (consumer.getState() != Thread.State.TIMED_WAITING && System.nanoTime() < end)
                Thread.sleep(1);
            if (consumer.getState() != Thread.State.TIMED_WAITING) throw new AssertionError("no wait");
            synchronized (b) {
                // Setting the interrupt first forces the wait's exceptional exit. Holding b
                // keeps the consumer out until stop() has published stop=true too.
                consumer.interrupt();
                long interruptedEnd = System.nanoTime() + TimeUnit.SECONDS.toNanos(1);
                while (consumer.getState() != Thread.State.BLOCKED
                        && System.nanoTime() < interruptedEnd) Thread.yield();
                if (consumer.getState() != Thread.State.BLOCKED)
                    throw new AssertionError("consumer did not leave its wait on interrupt");
                b.stop();
            }
            consumer.join(2000);
            if (consumer.isAlive()) throw new AssertionError("consumer did not end");
            System.out.println("consumer terminated after stop+interrupt: true");
            try {
                FileStream reopened = new FileStream(dir);
                reopened.close();
                System.out.println("underlying stream was closed");
            } catch (DirectoryInUseException e) {
                System.out.println("FAULT: terminated consumer left directory locked");
            }
        } finally {
            b.close();
            File[] files = dir.listFiles();
            if (files != null) for (File file : files) Files.deleteIfExists(file.toPath());
            Files.deleteIfExists(dir.toPath());
        }
    }
}
