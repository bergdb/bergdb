package bergdb.pubimp;

import java.util.Arrays;
import java.util.concurrent.atomic.AtomicLong;

/**
 * Probe (bergdb 016-06/S2): one collator of an index, as Index.kcollators and
 * FieldIndexFunction.kcollators hold it, used by several threads at once, as the
 * writers of several connections and the build's thread use it.
 * Counts sort bytes that differ from those of the same string computed alone.
 */
public class S2IcuThreads {
    public static void main(String[] args) throws Exception {
        final KCollator c = new OptionalIcuCollatorFactory().createCollator(args.length > 0 ? args[0] : "string/sv");
        System.out.println("collator: " + c.getClass().getName());
        final int n = 2000;
        final String[] strings = new String[n];
        final byte[][] expected = new byte[n][];
        java.util.Random r = new java.util.Random(1);
        for (int i = 0; i < n; i++) {
            StringBuilder b = new StringBuilder();
            int len = 3 + r.nextInt(30);
            for (int j = 0; j < len; j++) {
                b.append("abcdefghijklmnopqrstuvwxyzåäöÅÄÖéü ".charAt(r.nextInt(35)));
            }
            strings[i] = b.toString();
            expected[i] = c.getSortBytes(strings[i]);
        }
        final AtomicLong wrong = new AtomicLong();
        final AtomicLong errors = new AtomicLong();
        final AtomicLong total = new AtomicLong();
        Thread[] ts = new Thread[4];
        for (int t = 0; t < ts.length; t++) {
            final int seed = t;
            ts[t] = new Thread(() -> {
                java.util.Random rr = new java.util.Random(seed);
                long end = System.nanoTime() + 3_000_000_000L;
                while (System.nanoTime() < end) {
                    int i = rr.nextInt(n);
                    try {
                        byte[] got = c.getSortBytes(strings[i]);
                        if (!Arrays.equals(got, expected[i])) {
                            wrong.incrementAndGet();
                        }
                    } catch (RuntimeException e) {
                        errors.incrementAndGet();
                    }
                    total.incrementAndGet();
                }
            });
        }
        for (Thread t : ts) t.start();
        for (Thread t : ts) t.join();
        System.out.println("calls: " + total.get() + ", wrong sort bytes: " + wrong.get() + ", exceptions: " + errors.get());
    }
}
