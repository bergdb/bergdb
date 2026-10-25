package bergdb.core;

import java.io.OutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Random;

import bergdb.common.Bytes;
import bergdb.pub.util.Clock;
import bergdb.storage.MetaBlock;
import bergdb.storage.RecoverableStream;
import bergdb.stream.CutStream;
import bergdb.stream.MemoryStream;

/**
 * Probe of bergdb 005-39: what RecoverableStream.getPosOfTransCompletedBefore(spos) gives,
 * against its Javadoc ("the last valid transaction that was completely written before
 * stream position 'spos'", and the TODO under it), and what the iterators that start
 * there do in a stream whose front is cut.
 *
 * A: committed transactions of 1000 bytes, about 1.3 MB, each named by the meta blocks
 * after it, as NodeStream.appendNodes() does. B: the first transaction failed. C: stream
 * A cut at 1,000,000 (MemoryStream cuts at its 1 MB arrays, FileStream at its files, both
 * at a meta block). D: a database with reclaim on a CutStream, cut where Reclaim says, as
 * in Reclaim.Tester.testRestartAfterCut: NodeStream's iterators and print().
 *
 * Usage: java -ea -cp DIR:bergdb.jar bergdb.core.CompletedBeforeProbe
 */
public class CompletedBeforeProbe {
    static final int D = RecoverableStream.META_BLOCK_DISTANCE;

    public static void main(String[] args) throws Exception {
        MemoryStream ms = new MemoryStream();
        RecoverableStream r = new RecoverableStream(ms, new MetaBlock());
        ArrayList<long[]> ts = new ArrayList<long[]>();     // {start, end}
        while (ms.getLength() < 1300000) {
            long p = r.getNextSpos();
            r.append(trans(1000, RecoverableStream.LAST_BYTE), 0, 1000, true, -1);
            r.getMetaBlock().setLastTransSpos(p);
            ts.add(new long[] {p, RecoverableStream.getSpos(p, 1000)});
        }

        System.out.println("A: " + ts.size() + " transactions, stream length "
                + ms.getLength());
        for (long spos : new long[] {100, 150000, 200000, 200100, 399000, 600000}) {
            long got = r.getPosOfTransCompletedBefore(spos);
            System.out.println("  spos " + spos + ": got " + got
                    + ", the last completed before spos " + lastBefore(ts, spos)
                    + ", completed between them " + between(ts, got, spos));
        }
        int n = 0, isLast = 0, maxBetween = 0;
        for (long spos = 0; spos < ms.getLength(); spos += 997) {
            long got = r.getPosOfTransCompletedBefore(spos);
            n++;
            isLast += got == lastBefore(ts, spos) ? 1 : 0;
            maxBetween = Math.max(maxBetween, between(ts, got, spos));
        }
        System.out.println("  spos every 997 bytes: " + n + " positions; got the last one "
                + "completed before spos at " + isLast + "; at most " + maxBetween
                + " completed between them");

        MemoryStream ms2 = new MemoryStream();
        RecoverableStream r2 = new RecoverableStream(ms2, new MetaBlock());
        r2.append(trans(1000, (byte) 0), 0, 1000, false, -1);
        long p2 = r2.getNextSpos();
        r2.append(trans(1000, RecoverableStream.LAST_BYTE), 0, 1000, true, -1);
        System.out.println("B: first transaction failed; spos 5000: got "
                + r2.getPosOfTransCompletedBefore(5000) + ", the committed one at " + p2);

        ms.pretruncate(1000000);
        System.out.println("C: stream A cut, first position " + ms.getFirstPos());
        for (long spos : new long[] {0, 500, 1000000, 1050000, 1199999, 1200000, 1250000}) {
            try {
                long got = r.getPosOfTransCompletedBefore(spos);
                r.read(got, new byte[4], 0, 4);
                System.out.println("  spos " + spos + ": got " + got + ", can be read");
            } catch (Throwable e) {
                System.out.println("  spos " + spos + ": " + e);
            }
        }

        probeDatabase();
    }

    static void probeDatabase() {
        CoreTestClock clock = new CoreTestClock();
        long time = Clock.UNITS_PER_SEC;
        clock.setTime(time);
        CutStream stream = new CutStream();
        Db db = Db.builder().testSetup(stream).clock(clock).maxNodeSize8()
                .startupDistance(2000).start();
        db.setRetainDuration(1 * Clock.UNITS_PER_SEC);
        Random rnd = new Random(2);
        int count = 0;
        for (; count < 20000 && (stream.getCut() == 0
                || stream.getLength() < (stream.getCut() / D + 2) * D); count++) {
            time += Clock.UNITS_PER_SEC / 20;
            clock.setTime(time);
            byte[] v = new byte[1 + rnd.nextInt(30)];
            rnd.nextBytes(v);
            db.execute(db.trans().put("/k/" + rnd.nextInt(50), v).build());
        }
        db.sync(SyncLevel.STRONG);

        synchronized (db.internal().getWriteLock()) {
            NodeStream ns = db.internal().nodeStream();
            long cut = stream.getCut();
            long startupPos = db.internal().getStartupPosForEvict();
            System.out.println("D: " + count + " transactions, cut at " + cut
                    + ", first position " + ns.getFirstPos() + ", stream length "
                    + stream.getLength() + ", startup pos " + startupPos);
            System.out.println("  createTransIteratorFromExactStartupPos(" + startupPos + "): "
                    + iterate(ns.createTransIteratorFromExactStartupPos(startupPos)));
            for (long pos : new long[] {0, cut, cut + 1, (cut / D + 1) * D + 1000,
                    startupPos}) {
                System.out.println("  createTransIterator(" + pos + "): "
                        + iterate(ns.createTransIterator(pos)));
            }
            try {
                ns.print(new PrintStream(OutputStream.nullOutputStream()), 0);
                System.out.println("  print(out, 0): OK");
            } catch (Throwable e) {
                System.out.println("  print(out, 0): " + e);
            }
        }
        db.close();
    }

    /** The first transaction, the last one and the count, or what is thrown. */
    static String iterate(NodeStream.TransIterator ti) {
        try {
            long first = -1, last = -1;
            int n = 0;
            while (ti.next()) {
                if (first == -1) {
                    first = ti.tpos;
                }
                last = ti.tpos;
                n++;
            }
            return n + " transactions, " + first + " to " + last;
        } catch (Throwable e) {
            return e.toString();
        }
    }

    static byte[] trans(int size, byte last) {
        byte[] b = new byte[size];
        Bytes.intToBytesLE(size, b, 0);
        b[size - 1] = last;
        return b;
    }

    /** The start of the last transaction that ends at or before spos, or -1. */
    static long lastBefore(ArrayList<long[]> ts, long spos) {
        long result = -1;
        for (long[] t : ts) {
            if (t[1] <= spos) {
                result = t[0];
            }
        }
        return result;
    }

    /** The transactions after the one at 'from' that end at or before spos. */
    static int between(ArrayList<long[]> ts, long from, long spos) {
        int result = 0;
        for (long[] t : ts) {
            if (t[0] > from && t[1] <= spos) {
                result++;
            }
        }
        return result;
    }
}
