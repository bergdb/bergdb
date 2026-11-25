import bergdb.core.*;
import bergdb.dag.*;
import bergdb.stream.*;
import bergdb.pub.util.*;
import java.io.File;
import java.util.*;

/**
 * StmWindow (031-02, e8). The Core's optimistic transactions at the edge of the record of
 * recent writes ("the hashes of the last 96,000 to 128,000 key writes", Db, "Optimistic
 * transactions"). Each trial reads a key K at a read time t0, then other transactions
 * write K (or a virtual write hash that the reader reads, or nothing) at a random place
 * among M writes of other keys, M from 0 to 200,000, in transactions of 1 to 500 keys; then
 * the reader's transaction, with t0 and K's read, is executed. When K was written after t0
 * it must be refused with RerunException, whatever M (a commit would lose that write); when
 * nothing wrote K it may be refused only once M passes 96,000 (a read time older than the
 * record covers). Also after a restart: a read time before the start's last recovered
 * transaction is refused. The oracle checks the value of K after each trial.
 *
 * Usage: java StmWindow DIR|mem SEED TRIALS
 */
public class StmWindow {
    static void fail(String m) {
        System.out.println("STMWINDOW FAILED: " + m);
        System.out.flush();
        System.exit(1);
    }

    static Db db;
    static String dir;

    static void open(boolean fresh) throws Exception {
        if (dir.equals("mem")) db = Db.builder().mainStream(new MemoryStream()).start();
        else {
            if (fresh) deleteDir(new File(dir));
            db = Db.builder().mainStream(new FileStream(new File(dir))).start();
        }
    }

    static void deleteDir(File d) {
        File[] fs = d.listFiles();
        if (fs != null) for (File f : fs) f.delete();
        d.delete();
    }

    public static void main(String[] args) throws Exception {
        dir = args[0];
        long seed = Long.parseLong(args[1]);
        int trials = Integer.parseInt(args[2]);
        Random r = new Random(seed);
        System.out.println("StmWindow seed " + seed + " trials " + trials);
        open(true);
        long nConflict = 0, nRefusedOld = 0, nTakenClean = 0, maxTakenM = -1, minRefusedCleanM = Long.MAX_VALUE;
        long counter = 0;
        long otherKeys = 0;
        for (int trial = 0; trial < trials; trial++) {
            if (trial % 15 == 14) { db.close(); open(true); counter = 0; }
            byte[] k = ("K" + (trial % 7)).getBytes();
            long[] ks = Keys.toSegments(k);
            GetData gd = db.newGetData();
            byte[] cur = db.getOne(Long.MAX_VALUE, ks, gd);
            counter = cur == null ? 0 : ByteUtil.get(cur);
            long t0 = db.currentTime();
            byte[] read = db.getOne(t0, ks, gd);
            long readVal = read == null ? 0 : ByteUtil.get(read);
            if (readVal != counter) fail("read at t0 " + readVal + ", expected " + counter);
            int mode = r.nextInt(6);        // 0 nothing writes K, 1 K written, 2 virtual hash, 3 restart,
                                            // 4 and 5: K written last, read at its time or one before
            int m;
            int w = r.nextInt(10);
            if (w < 6) m = 80_000 + r.nextInt(60_000);
            else if (w < 8) m = r.nextInt(80_000);
            else m = 140_000 + r.nextInt(60_000);
            int pos = r.nextInt(m + 1);    // where K's write goes among the M writes
            if (r.nextInt(5) == 0) pos = m;   // the last
            if (r.nextInt(5) == 0) pos = 0;   // the first
            long vhash = 0x5A5A0000L + trial;
            int written = 0;
            boolean kWritten = false;
            while (written < m || ((mode == 1 || mode == 2) && !kWritten)) {
                int n = 1 + r.nextInt(500);
                Trans.Builder b = db.trans();
                int inThis = 0;
                for (int i = 0; i < n && written < m; i++) {
                    if ((mode == 1 || mode == 2) && !kWritten && written == pos) break;
                    b.put(("o" + (otherKeys++ % 400_000)).getBytes(), new byte[] {(byte) i});
                    written++; inThis++;
                }
                if ((mode == 1 || mode == 2) && !kWritten && written == pos) {
                    if (mode == 1) { counter += 1000; b.put(k, ByteUtil.bytes(counter)); }
                    else b.addVirtualWriteHash(vhash);
                    kWritten = true;
                    inThis++;
                }
                if (inThis > 0) db.execute(b.build());
            }
            if (mode == 3) { db.close(); open(false); }
            if (mode == 4 || mode == 5) {
                // Read K at the time of the transaction that writes it, or one unit before.
                counter += 1000;
                Trans tk = db.trans().put(k, ByteUtil.bytes(counter)).build();
                db.execute(tk);
                long tr = mode == 4 ? tk.tt : tk.tt - 1;
                byte[] rv = db.getOne(tr, ks, gd);
                long rval = rv == null ? 0 : ByteUtil.get(rv);
                long expect = mode == 4 ? counter : counter - 1000;
                if (rval != expect) fail("trial " + trial + ": read at " + (mode == 4 ? "the write's time" : "one before")
                        + " gives " + rval + ", expected " + expect);
                Trans.Builder b4 = db.trans().lookupTime(tr).keyRead(ks).put(k, ByteUtil.bytes(rval + 1));
                boolean taken4;
                try { db.execute(b4.build()); taken4 = true; } catch (RerunException e) { taken4 = false; }
                if (mode == 5 && taken4) fail("trial " + trial + ": a reader one unit before K's write was taken: a lost update");
                if (mode == 4 && !taken4) fail("trial " + trial + ": a reader at K's write time refused after "
                        + m + " other writes");
                if (taken4) counter = rval + 1;
                byte[] nv = db.getOne(Long.MAX_VALUE, ks, gd);
                if ((nv == null ? 0 : ByteUtil.get(nv)) != counter) fail("trial " + trial + ": K after the boundary reader");
                if (taken4) nTakenClean++; else nConflict++;
                continue;
            }
            // The reader's transaction.
            Trans.Builder b = db.trans().lookupTime(t0).keyRead(ks);
            if (mode == 2) b.addReadHash(vhash);
            b.put(k, ByteUtil.bytes(readVal + 1));
            boolean taken;
            try {
                db.execute(b.build());
                taken = true;
            } catch (RerunException e) {
                taken = false;
            }
            if (taken && (mode == 1 || mode == 2)) fail("trial " + trial + ": the reader at t0 was taken although "
                    + (mode == 1 ? "K" : "its read hash") + " was written after t0, at " + pos + " of " + m
                    + " other key writes: a lost update");
            if (taken && mode == 3 && m > 0) fail("trial " + trial + ": a read time before the restart was taken");
            if (taken) {
                counter = readVal + 1;
                nTakenClean++;
                maxTakenM = Math.max(maxTakenM, m);
            } else if (mode == 0) {
                nRefusedOld++;
                minRefusedCleanM = Math.min(minRefusedCleanM, m);
                if (m < 96_000 - 500) fail("trial " + trial + ": refused with nothing written to K after " + m
                        + " other key writes, fewer than 96,000");
            } else nConflict++;
            byte[] now = db.getOne(Long.MAX_VALUE, ks, db.newGetData());
            long nowVal = now == null ? 0 : ByteUtil.get(now);
            if (nowVal != counter) fail("trial " + trial + ": K is " + nowVal + ", expected " + counter);
            if (trial % 20 == 0) System.out.println("  trial " + trial + ": conflicts refused " + nConflict
                    + ", clean taken " + nTakenClean + " (largest M " + maxTakenM + "), clean refused as too old "
                    + nRefusedOld + " (smallest M " + (minRefusedCleanM == Long.MAX_VALUE ? "-" : minRefusedCleanM) + ")");
        }
        db.close();
        System.out.println("conflicts refused " + nConflict + ", clean taken " + nTakenClean + " (largest M " + maxTakenM
                + "), clean refused as too old " + nRefusedOld + " (smallest M " + minRefusedCleanM + ")");
        System.out.println("STMWINDOW OK");
    }

    static final class ByteUtil {
        static byte[] bytes(long v) {
            byte[] b = new byte[8];
            for (int i = 0; i < 8; i++) b[i] = (byte) (v >>> (56 - 8 * i));
            return b;
        }
        static long get(byte[] b) {
            long v = 0;
            for (int i = 0; i < 8; i++) v = (v << 8) | (b[i] & 0xff);
            return v;
        }
    }
}
