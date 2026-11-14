package bergdb.core;

import java.io.EOFException;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.Locale;
import java.util.Random;
import java.util.SplittableRandom;

import bergdb.dag.Node;
import bergdb.dag.ValueNode;
import bergdb.stream.AppendOnlyStream;

/**
 * Can TransSeq.take's byte limit ('maxBytes', the room left in the record) stop a take past
 * the deadline (bergdb 028-12)? A probe of the item: it uses bergdb.jar as it is, through
 * Db.testHooks, in package bergdb.core for TransSeq's fields and StoredTrans.recordLimit.
 * In memory, no eviction; the stream keeps its last 'ring' bytes, as 007-06's WriteBench.
 *
 * After every record it checks the take of that record. Before the record, the stream's
 * length is L (the record's tpos) and the section's span is the newest tpos minus the oldest
 * (from the last check), so the take's deadline is hardSp = L - max(2 sd, span). If the
 * oldest transaction left after the take begins at or before hardSp, the take stopped past
 * the deadline, which only the byte limit does: a "stop". It also logs the largest span after
 * a take (the section without its last record, T3's quantity) in sd, the debt (the sum of
 * TransSeq.recordBytes over the section, the take's own measure of D, walked every sd/200 of
 * stream and at every stop), and the room: the record limit less the record's bytes other
 * than the nodes it took (its own part; the record's framing counts in it too, a bound).
 * It counts the records whose take took a transaction past the deadline, and the largest
 * got-dirty set of one transaction in bytes (TransSeq.recordBytes), when it was added and
 * when it was taken: 005-31's premise is that one fits in the room. And the most due bytes
 * one take took (the nodes of its transactions past the deadline), also against its room.
 *
 * Options (-Dtb.x=y): keys (1000000), sd (50000000), tx (500, puts a load transaction, L1),
 * utx (500, puts an update transaction), updates (10000000, random puts to loaded keys),
 * recordLimit (StoredTrans.recordLimit, default the real one, 2^31 - 9), big (0: none; else
 * values of that many bytes in all, in KVs of at most 8 MiB (L4; L5 allows 32 MiB a
 * transaction), in a transaction after every bigEvery-th update transaction: the costly
 * record of 028-12's case 2), bigEvery (100), bigCount (50, the most costly transactions:
 * every version stays in memory), ring (1000000000).
 */
public class TakeBytesProbe {
    static String prop(String n, String d) { return System.getProperty("tb." + n, d); }

    final int keys = Integer.parseInt(prop("keys", "1000000"));
    final int sd = Integer.parseInt(prop("sd", "50000000"));
    final int tx = Integer.parseInt(prop("tx", "500"));
    final int utx = Integer.parseInt(prop("utx", "500"));
    final long updates = Long.parseLong(prop("updates", "10000000"));
    final long recordLimit = Long.parseLong(prop("recordLimit", "" + StoredTrans.MAX_RECORD_SIZE));
    final int big = Integer.parseInt(prop("big", "0"));
    final int bigEvery = Integer.parseInt(prop("bigEvery", "100"));
    final int bigCount = Integer.parseInt(prop("bigCount", "50"));
    final long ring = Long.parseLong(prop("ring", "1000000000"));

    final CoreTestClock clock = new CoreTestClock();
    long time = bergdb.pub.util.Clock.UNITS_PER_SEC;
    Db db;
    int phase;                      // 0 load, 1 updates
    static java.lang.reflect.Field firstField;

    // State after the last record's take.
    TransSeq.TransInfo prevFirst;   // the oldest transaction of the section, or null
    long prevFirstTpos, prevLastTpos;
    boolean prevEmpty = true;

    long records, stops, lastWalk, maxDebt, maxRecord, maxTaken;
    long minRoom = Long.MAX_VALUE;
    long maxSpan, maxSpanAt;
    double maxDebtPerRoom;
    long[] phaseMaxDebt = new long[2];
    long[] phaseMaxSpan = new long[2];
    long[] phaseStops = new long[2];
    long[] deadlineRecords = new long[2];   // records whose take took a transaction past the deadline
    long maxTx, maxTxAdded;     // the largest got-dirty set of one transaction: when taken, when added
    long maxDue;                // the most due bytes one take took
    double maxDueRoom;          // the most due bytes one take took, against its room

    /** Keeps the last 'ring' bytes. */
    static final class RingStream implements AppendOnlyStream {
        final byte[] buf;
        long length;
        RingStream(long size) { buf = new byte[(int) size]; }
        public long getLength() { return length; }
        public long getFirstPos() { return 0; }
        public synchronized void read(long p, byte[] d, int o, int n) throws IOException {
            if (p + n > length) throw new EOFException("read past end " + p);
            if (p < length - buf.length) throw new IOException("read before the ring: " + p);
            for (int i = 0; i < n; i++) d[o + i] = buf[(int) ((p + i) % buf.length)];
        }
        public synchronized void append(byte[] s, int o, int n) {
            int at = (int) (length % buf.length);
            int first = Math.min(n, buf.length - at);
            System.arraycopy(s, o, buf, at, first);
            if (first < n) System.arraycopy(s, o + first, buf, 0, n - first);
            length += n;
        }
        public void pretruncate(long p) {}
        public void seekFirstPos(long p) {}
        public void close() {}
    }

    static byte[] key(int k) {
        byte[] b = new byte[24];
        System.arraycopy("/scale/key/".getBytes(StandardCharsets.US_ASCII), 0, b, 0, 11);
        long v = k;
        for (int i = 23; i >= 11; i--) { b[i] = (byte) ('0' + v % 10); v /= 10; }
        return b;
    }

    TransSeq.TransInfo first() {
        try {
            return (TransSeq.TransInfo) firstField.get(db.internal().transSeq());
        } catch (ReflectiveOperationException e) {
            throw new RuntimeException(e);
        }
    }

    long debt() {
        long d = 0;
        for (TransSeq.TransInfo t = first(); t != null; t = t.next) d += TransSeq.recordBytes(t);
        return d;
    }

    void recordWritten(Db.ExecuteData x) {
        records++;
        final long L = x.trans.tpos;
        final long recordBytes = x.trans.nextPos - x.trans.tpos;
        final TransSeq.TransInfo f = first();      // after the take; the new one is last
        // The take's deadline, as TransSeq.take computed it before the record.
        final long hardSp = L - Math.max(2L * sd, prevLastTpos - prevFirstTpos);
        // The nodes this record took: the transactions from the old first to the new first.
        long taken = 0;
        boolean byDeadline = false;
        long due = 0;           // the bytes taken of transactions past the deadline
        if (!prevEmpty) {
            for (TransSeq.TransInfo t = prevFirst; t != null && t != f && t != x.transInfo; t = t.next) {
                final long c = TransSeq.recordBytes(t);
                taken += c;
                maxTx = Math.max(maxTx, c);
                if (t.tpos <= hardSp) {
                    byDeadline = true;
                    due += c;
                }
            }
        }
        if (byDeadline) deadlineRecords[phase]++;
        maxTxAdded = Math.max(maxTxAdded, TransSeq.recordBytes(x.transInfo));
        final long room = recordLimit - (recordBytes - taken);
        maxDue = Math.max(maxDue, due);
        maxDueRoom = Math.max(maxDueRoom, (double) due / room);
        minRoom = Math.min(minRoom, room);
        maxRecord = Math.max(maxRecord, recordBytes);
        maxTaken = Math.max(maxTaken, taken);
        // A stop past the deadline: the oldest left was due.
        if (!prevEmpty && f != null && f != x.transInfo) {
            if (f.tpos <= hardSp) {
                stops++;
                phaseStops[phase]++;
                if (stops <= 20 || stops % 1000 == 0) {
                    final long debt = debt();
                    System.out.println(String.format(Locale.ROOT, "STOP %d at record %d (phase %d): due %d bytes"
                            + " before the deadline, its nodes %d bytes, taken %d, room %d, debt %d (%.2f room),"
                            + " span %.2f sd", stops, records, phase, hardSp - f.tpos, TransSeq.recordBytes(f),
                            taken, room, debt, (double) debt / room, (double) (L - f.tpos) / sd));
                }
            }
        }
        if (f != null && f != x.transInfo) {
            final long span = L - f.tpos;       // R(s+1) .. R(k-1): the section without its last record
            if (span > maxSpan) { maxSpan = span; maxSpanAt = records; }
            phaseMaxSpan[phase] = Math.max(phaseMaxSpan[phase], span);
        }
        if (x.trans.nextPos - lastWalk >= Math.max(65536, sd / 200)) {
            lastWalk = x.trans.nextPos;
            final long debt = debt();
            maxDebt = Math.max(maxDebt, debt);
            phaseMaxDebt[phase] = Math.max(phaseMaxDebt[phase], debt);
            maxDebtPerRoom = Math.max(maxDebtPerRoom, (double) debt / room);
        }
        // The state for the next record's take.
        prevFirst = f;
        prevEmpty = f == null;
        prevFirstTpos = f == null ? 0 : f.tpos;
        prevLastTpos = x.transInfo.tpos;
    }

    void run() throws Exception {
        firstField = TransSeq.class.getDeclaredField("first");
        firstField.setAccessible(true);
        StoredTrans.recordLimit = recordLimit;
        clock.setTime(time);
        DbBuilder b = Db.builder().stream("main", new RingStream(ring)).clock(clock).testId().noEvict();
        b.startupDistance(sd);
        db = b.build();
        db.start();
        Db.testHooks = new Db.TestHooks() {
            public void transExecuted(Db.ExecuteData x) { recordWritten(x); }
            public void valueNodeCreated(ValueNode node, long[] key) {}
            public void nodeTouched(Node node) {}
            public void nodeReplaced(Node node) {}
        };
        System.out.println(String.format(Locale.ROOT, "TakeBytesProbe: %d keys, sd %d, tx %d, utx %d, updates %d,"
                + " record limit %d, big %d every %d", keys, sd, tx, utx, updates, recordLimit, big, bigEvery));
        int[] ord = new int[keys];
        for (int i = 0; i < keys; i++) ord[i] = i;
        Random rnd = new Random(1);
        for (int i = keys - 1; i > 0; i--) { int j = rnd.nextInt(i + 1); int t = ord[i]; ord[i] = ord[j]; ord[j] = t; }
        long t0 = System.nanoTime();
        byte[] value = new byte[8];
        for (int i = 0; i < keys; i += tx) {
            Trans.Builder tb = db.trans();
            int e = Math.min(keys, i + tx);
            for (int j = i; j < e; j++) {
                int k = ord[j];
                value[0] = (byte) (k >>> 24); value[1] = (byte) (k >>> 16); value[2] = (byte) (k >>> 8); value[3] = (byte) k;
                tb.put(key(k), value.clone());
            }
            time += bergdb.pub.util.Clock.UNITS_PER_SEC / 10000;
            clock.setTime(time);
            db.execute(tb.build());
        }
        report("load");
        phase = 1;
        SplittableRandom ur = new SplittableRandom(2);
        value[4] = 1;
        long n = 0;
        for (long i = 0; i < updates; i += utx) {
            Trans.Builder tb = db.trans();
            long e = Math.min(updates, i + utx);
            for (long j = i; j < e; j++) {
                int k = ur.nextInt(keys);
                value[0] = (byte) (k >>> 24); value[1] = (byte) (k >>> 16); value[2] = (byte) (k >>> 8); value[3] = (byte) k;
                tb.put(key(k), value.clone());
            }
            time += bergdb.pub.util.Clock.UNITS_PER_SEC / 10000;
            clock.setTime(time);
            db.execute(tb.build());
            n++;
            if (big > 0 && n % bigEvery == 0 && n / bigEvery <= bigCount) {
                Trans.Builder bb = db.trans();
                for (int left = big, m = 0; left > 0; m++) {
                    byte[] v = new byte[Math.min(left, Db.MAX_VALUE_BYTES - 64)];
                    v[0] = (byte) n;
                    left -= v.length;
                    bb.put(("/big/key" + m).getBytes(StandardCharsets.US_ASCII), v);
                }
                db.execute(bb.build());
            }
        }
        report("updates");
        System.out.println(String.format(Locale.ROOT, "total: %d records, %.1f s", records, (System.nanoTime() - t0) / 1e9));
        Db.testHooks = null;
        db.close();
        StoredTrans.recordLimit = StoredTrans.MAX_RECORD_SIZE;
        System.out.println("TAKEBYTESPROBE OK");
    }

    void report(String what) {
        long end = db.internal().nodeStream().getNextPos();
        System.out.println(String.format(Locale.ROOT, "%s: stream %d, records %d; stops past the deadline %d (all %d);"
                + " span max %.3f sd (this phase %.3f); debt max %d (this phase %d, %.3f sd); room min %d;"
                + " debt / room max %.4f; largest record %d, largest take %d; records the deadline took in %d;"
                + " largest transaction's nodes %d when taken, %d when added;"
                + " due taken max %d bytes, against the room %.4f",
                what, end, records, phaseStops[phase], stops, (double) maxSpan / sd, (double) phaseMaxSpan[phase] / sd,
                maxDebt, phaseMaxDebt[phase], (double) phaseMaxDebt[phase] / sd, minRoom, maxDebtPerRoom,
                maxRecord, maxTaken, deadlineRecords[phase], maxTx, maxTxAdded, maxDue, maxDueRoom));
    }

    public static void main(String[] args) throws Exception {
        new TakeBytesProbe().run();
    }
}
