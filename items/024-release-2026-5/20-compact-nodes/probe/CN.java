package bergdb.core;

import java.io.*;
import java.util.*;

import bergdb.pub.util.SyncLevel;
import bergdb.stream.FileStream;

/**
 * The stream maker of bergdb 024-20, written 2026-11-11: a database made by one workload, then
 * Scan over the window of its last phase. The Core API, a FileStream with the builder's
 * defaults (sd 50 MB unless sd= is given), a test clock of dt a transaction.
 *
 * java -cp DIR:bergdb.jar bergdb.core.CN key=value...
 *   n       keys (1000000)
 *   work    seq: fill in key order; rand: fill in random order;
 *           over: rand, then ops random overwrites of live keys;
 *           fifo: seq, then ops operations of a queue: deletes of the oldest keys and puts of
 *                 new ones at the end, half and half, with reclaim (retain= seconds);
 *           del:  rand, then ops deletes of random keys
 *   batch   operations a transaction (100)
 *   fbatch  the fill's batch for over, fifo and del (100); seq and rand fill with batch
 *   key     short: 4 bytes, big-endian binary (one segment); k24: "/app/users/k" + 12 digits
 *   vsize   value bytes (100), random
 *   ops     operations of the phase after the fill (n)
 *   retain  seconds of reclaim's retention (fifo only; 0: forever)
 *   sd      startup distance in bytes (the builder's default)
 *   dir     the database directory, removed at the end unless keep=1
 */
public class CN {
    final Map<String, String> p = new HashMap<String, String>();
    int i(String k, int d) { return p.containsKey(k) ? Integer.parseInt(p.get(k)) : d; }
    long l(String k, long d) { return p.containsKey(k) ? Long.parseLong(p.get(k)) : d; }
    String s(String k, String d) { return p.containsKey(k) ? p.get(k) : d; }

    static final long SEC = CoreTestClock.UNITS_PER_SEC;
    final long t0 = System.nanoTime();
    CoreTestClock clock;
    long time = 10 * SEC;
    long dt;
    Db db;
    String keyKind;
    int vsize;
    final Random vr = new Random(5);
    long txs, opsAll;

    String el() { return String.format("[%.1fs]", (System.nanoTime() - t0) / 1e9); }

    byte[] key(long k) {
        if (keyKind.equals("short")) {
            return new byte[] {(byte) (k >>> 24), (byte) (k >>> 16), (byte) (k >>> 8), (byte) k};
        }
        return String.format("/app/users/k%012d", k).getBytes();
    }

    byte[] value() {
        byte[] v = new byte[vsize];
        vr.nextBytes(v);
        return v;
    }

    long[] txPos = new long[1 << 16];
    int[] txOps = new int[1 << 16];
    int txN;

    void exec(Trans.Builder b, int ops) {
        time += dt;
        clock.setTime(time);
        Trans t = b.build();
        db.execute(t);
        txs++;
        opsAll += ops;
        if (txN == txPos.length) {
            txPos = Arrays.copyOf(txPos, 2 * txN);
            txOps = Arrays.copyOf(txOps, 2 * txN);
        }
        txPos[txN] = t.tpos;
        txOps[txN++] = ops;
    }

    /** The user operations of the transactions whose records are at or after pos. */
    long opsFrom(long pos) {
        long o = 0;
        for (int k = 0; k < txN; k++) if (txPos[k] >= pos) o += txOps[k];
        return o;
    }

    static void shuffle(int[] o, long seed) {
        Random r = new Random(seed);
        for (int k = o.length - 1; k > 0; k--) {
            int j = r.nextInt(k + 1);
            int t = o[k]; o[k] = o[j]; o[j] = t;
        }
    }

    void fill(int[] o, int batch) {
        for (int k = 0; k < o.length; ) {
            Trans.Builder b = db.trans();
            int c = 0;
            for (int j = 0; j < batch && k < o.length; j++, k++, c++) b.put(key(o[k]), value());
            exec(b, c);
        }
    }

    void run() throws IOException {
        final int n = i("n", 1000000);
        final String work = s("work", "rand");
        final int batch = i("batch", 100);
        keyKind = s("key", "k24");
        vsize = i("vsize", 100);
        final int ops = i("ops", n);
        dt = l("dtus", 1000) * 10;      // 100 ns units; 1 ms a transaction by default
        File dir = new File(s("dir", "data"));
        rm(dir);
        dir.mkdirs();
        clock = new CoreTestClock();
        clock.setTime(time);
        DbBuilder bl = Db.builder().mainStream(new FileStream(dir)).clock(clock);
        if (p.containsKey("sd")) bl.startupDistance(i("sd", 50000000));
        if (i("ns", 30) == 62) bl.maxNodeSize62();
        if (i("ns", 30) == 14) bl.maxNodeSize14();
        db = bl.start();
        String label = s("label", work + "-b" + batch + "-" + keyKind + "-v" + vsize + "-n" + n);
        System.out.println("CN " + label + " " + p);
        int[] o = new int[n];
        for (int k = 0; k < n; k++) o[k] = k;
        boolean random = !work.equals("seq") && !work.equals("fifo");
        if (random) shuffle(o, 1);
        // the fill's batch: the phase workloads fill with 100 a transaction unless fbatch= says
        boolean phased = !work.equals("seq") && !work.equals("rand");
        fill(o, phased ? i("fbatch", 100) : batch);
        long fillOps = opsAll, fillTx = txs, fillLen = db.getStreamLength();
        System.out.printf("%s FILL ops=%d tx=%d len=%d bytes/op=%.1f%n", el(), fillOps, fillTx,
                fillLen, (double) fillLen / fillOps);
        long from = 0, phaseOps = fillOps;
        if (!work.equals("seq") && !work.equals("rand")) {
            from = db.getStreamLength();
            long op0 = opsAll, len0 = db.getStreamLength();
            if (work.equals("fifo") && l("retain", 0) > 0) db.setRetainDuration(l("retain", 0) * SEC);
            Random r = new Random(11);
            long head = 0, next = n;
            int done = 0;
            if (work.equals("over")) {
                while (done < ops) {
                    Trans.Builder b = db.trans();
                    HashSet<Integer> u = new HashSet<Integer>();
                    while (u.size() < Math.min(batch, ops - done)) u.add(r.nextInt(n));
                    for (int x : u) b.put(key(x), value());
                    exec(b, u.size());
                    done += u.size();
                }
            } else if (work.equals("fifo")) {
                long flip = 0;
                while (done < ops) {
                    Trans.Builder b = db.trans();
                    int c = Math.min(batch, ops - done);
                    for (int j = 0; j < c; j++) {
                        if (((flip++) & 1) == 0) b.delete(key(head++));
                        else b.put(key(next++), value());
                    }
                    exec(b, c);
                    done += c;
                }
            } else if (work.equals("del")) {
                int[] d = Arrays.copyOf(o, n);
                shuffle(d, 7);
                while (done < Math.min(ops, n)) {
                    Trans.Builder b = db.trans();
                    int c = Math.min(batch, Math.min(ops, n) - done);
                    for (int j = 0; j < c; j++) b.delete(key(d[done + j]));
                    exec(b, c);
                    done += c;
                }
            }
            phaseOps = opsAll - op0;
            System.out.printf("%s PHASE %s ops=%d len=%d bytes/op=%.1f first=%d kept=%d iters=%d%n",
                    el(), work, phaseOps, db.getStreamLength(),
                    (double) (db.getStreamLength() - len0) / phaseOps, db.getFirstAvailablePos(),
                    db.getStreamLength() - db.getFirstAvailablePos(), db.getReclaimIterationCount());
            if (work.equals("fifo") && db.getFirstAvailablePos() > from) {
                // the window is the stream kept: from the cut; its user operations are those
                // of the transactions there (reclaim's own records are in the window too)
                from = db.getFirstAvailablePos();
                phaseOps = opsFrom(from);
            }
        }
        db.sync(SyncLevel.ORDINARY);
        db.close();
        System.out.flush();
        Scan.run(dir, from, phaseOps, i("deflate", 1), label, System.out, s("dump", null),
                i("dumpn", 200000));
        if (i("keep", 0) == 0) rm(dir);
        System.out.printf("%s DONE%n", el());
    }

    static void rm(File f) {
        File[] fs = f.listFiles();
        if (fs != null) for (File c : fs) rm(c);
        f.delete();
    }

    public static void main(String[] args) throws Exception {
        CN x = new CN();
        for (String a : args) {
            int k = a.indexOf('=');
            x.p.put(a.substring(0, k), a.substring(k + 1));
        }
        x.run();
    }
}
