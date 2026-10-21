import java.util.Random;
import java.util.concurrent.atomic.AtomicLong;

import bergdb.storage.BufferedStream;
import bergdb.stream.MemoryStream;

/**
 * 005-14: does BufferedStream.close() ever append more bytes than were appended? A flush
 * of 0 bytes (flushAndClose set, nothing buffered, stop not yet set) appends the whole ring
 * buffer. THREADS threads, each ITER times: a stream of capacity 100, 7 bytes appended and
 * flushed, a random pause of 0 to 3 ms, close(), then a check of the length.
 * Usage: java -cp bergdb.jar:. CloseRace THREADS ITER
 */
public class CloseRace {
    public static void main(String[] args) throws Exception {
        final int threads = Integer.parseInt(args[0]);
        final int iter = Integer.parseInt(args[1]);
        final AtomicLong bad = new AtomicLong(), done = new AtomicLong();
        Thread[] ts = new Thread[threads];
        for (int t = 0; t < threads; t++) {
            final int seed = t;
            ts[t] = new Thread() {
                public void run() {
                    Random rnd = new Random(seed);
                    try {
                        for (int i = 0; i < iter; i++) {
                            MemoryStream m = new MemoryStream();
                            BufferedStream b = new BufferedStream(m, 100, 10);
                            b.start();
                            b.append(new byte[] {1, 2, 3, 4, 5, 6, 7}, 0, 7);
                            while (m.getLength() < 7) Thread.sleep(0, 200000);
                            long pause = rnd.nextInt(3000);
                            Thread.sleep(pause / 1000, (int) (pause % 1000) * 1000);
                            b.close();
                            Thread.sleep(5);        // A late flush lands before the check.
                            if (m.getLength() != 7) {
                                long n = bad.incrementAndGet();
                                if (n <= 5) System.out.println("BAD: length " + m.getLength() + " after close, 7 appended");
                            }
                            done.incrementAndGet();
                        }
                    } catch (Exception e) {
                        System.out.println("error " + e);
                    }
                }
            };
            ts[t].start();
        }
        for (Thread t : ts) t.join();
        System.out.println("closes " + done.get() + ", with more bytes than appended: " + bad.get());
    }
}
