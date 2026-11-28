import bergdb.core.*;
import bergdb.dag.*;
import bergdb.stream.*;
import bergdb.pub.util.*;
import java.util.*;

/**
 * StmBins (031-02, e9). Every position of the Core's record of recent writes, whatever its
 * inner boundaries: a run of single-key transactions (and of transactions of up to 500 keys)
 * each writes a key of its own, Ki at time ti; then, for every i whose write is among the
 * last 90,000, a reader that read Ki at ti - 1 must be refused with RerunException (Ki was
 * written after its read time: a commit would lose that write), and for a sample, a reader
 * that read Ki at ti, the time of the write itself, with fewer than 96,000 writes after it,
 * must be taken. A reader that is refused writes nothing; one that is taken writes a key of
 * its own, which the oracle checks.
 *
 * Usage: java StmBins SEED ROUNDS
 */
public class StmBins {
    static void fail(String m) {
        System.out.println("STMBINS FAILED: " + m);
        System.out.flush();
        System.exit(1);
    }

    public static void main(String[] args) throws Exception {
        long seed = Long.parseLong(args[0]);
        int rounds = Integer.parseInt(args[1]);
        Random r = new Random(seed);
        System.out.println("StmBins seed " + seed + " rounds " + rounds);
        long refused = 0, taken = 0;
        for (int round = 0; round < rounds; round++) {
            Db db = Db.builder().mainStream(new MemoryStream()).start();
            // Some writes before, so that the record has wrapped in some rounds.
            int pre = r.nextInt(3) == 0 ? 0 : r.nextInt(300_000);
            for (int i = 0; i < pre; i += 500) {
                Trans.Builder b = db.trans();
                for (int j = i; j < Math.min(pre, i + 500); j++) b.put(("pre" + j).getBytes(), new byte[] {1});
                db.execute(b.build());
            }
            int n = 100_000 + r.nextInt(30_000);
            long[] times = new long[n];
            byte[][] keys = new byte[n][];
            int i = 0;
            boolean multi = r.nextBoolean();
            while (i < n) {
                int m = multi ? 1 + r.nextInt(r.nextInt(4) == 0 ? 500 : 20) : 1;
                Trans.Builder b = db.trans();
                int first = i;
                for (int j = 0; j < m && i < n; j++, i++) {
                    keys[i] = ("r" + round + "k" + i).getBytes();
                    b.put(keys[i], new byte[] {(byte) i});
                }
                Trans t = b.build();
                db.execute(t);
                for (int j = first; j < i; j++) times[j] = t.tt;
            }
            // Writes after each i: n - 1 - i (each key one write).
            int from = Math.max(0, n - 90_000);
            for (int k = n - 1; k >= from; k--) {
                long[] seg = Keys.toSegments(keys[k]);
                Trans t = db.trans().lookupTime(times[k] - 1).keyRead(seg).put(("x" + k).getBytes(), new byte[] {2}).build();
                try {
                    db.execute(t);
                    fail("round " + round + ": a reader at " + (times[k] - 1) + " of key " + k + ", written at " + times[k]
                            + " with " + (n - 1 - k) + " writes after it" + (multi ? " (transactions of several keys)" : "")
                            + ", was taken: a lost update");
                } catch (RerunException e) {
                    refused++;
                }
            }
            // A sample at the write's own time, newest first, fewer than 96,000 writes after.
            int ok = 0;
            for (int q = 0; q < 300; q++) {
                int k = n - 1 - r.nextInt(Math.min(n, 80_000));
                long[] seg = Keys.toSegments(keys[k]);
                byte[] own = ("y" + round + "-" + q).getBytes();
                Trans t = db.trans().lookupTime(times[k]).keyRead(seg).put(own, new byte[] {3}).build();
                try {
                    db.execute(t);
                    taken++; ok++;
                } catch (RerunException e) {
                    fail("round " + round + ": a reader at the write's own time " + times[k] + " of key " + k + ", with "
                            + (n - 1 - k) + " writes after it and " + ok + " readers, was refused");
                }
                if (db.getOne(Long.MAX_VALUE, Keys.toSegments(own), db.newGetData()) == null) fail("the reader's key is missing");
            }
            for (int k = from; k < n; k += 997) {
                if (db.getOne(Long.MAX_VALUE, Keys.toSegments(("x" + k).getBytes()), db.newGetData()) != null) {
                    fail("a refused reader's key x" + k + " was written");
                }
            }
            db.close();
            System.out.println("  round " + round + " (" + (multi ? "multi" : "single") + ", " + pre + " before, " + n
                    + " keys): refused " + refused + ", taken " + taken);
        }
        System.out.println("STMBINS OK");
    }
}
