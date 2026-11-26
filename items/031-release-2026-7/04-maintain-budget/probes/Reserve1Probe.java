package bergdb.core;

import java.util.concurrent.atomic.AtomicLong;
import bergdb.pub.util.Clock;
import bergdb.stream.CutStream;

/**
 * bergdb 031-04: Codex's case of 031-03 (section 14, finding 1), where 031-03's drain
 * repeats: a step reserve of 1 (DbBuilder.reclaimStepReserve, a test setting), KEYS keys of
 * VAL bytes (Codex: 150 of 111) at node size 8, R = 1 s, startup distance SD, ROUNDS
 * overwrites of every key, then CALLS calls (a call a millisecond of a test clock; Codex:
 * a million). Prints the iterations, the bytes written by the calls in all and in their last
 * half, and the stream kept.
 *   java -cp out:bergdb.jar bergdb.core.Reclaim1Probe KEYS VAL SD ROUNDS CALLS [RESERVE]
 */
public class Reserve1Probe {
    public static void main(String[] a) throws Exception {
        final int keys = Integer.parseInt(a[0]), val = Integer.parseInt(a[1]);
        final int sd = Integer.parseInt(a[2]), rounds = Integer.parseInt(a[3]);
        final int calls = Integer.parseInt(a[4]);
        final long reserve = a.length > 5 ? Long.parseLong(a[5]) : 1;
        final long ms = Clock.UNITS_PER_SEC / 1000;
        final AtomicLong time = new AtomicLong(Clock.UNITS_PER_SEC);
        Db d = Db.builder().testSetup(new CutStream()).clock(time::get).maxNodeSize8()
                .reclaimStepReserve(reserve).start();
        d.setStartupDistance(sd);
        d.setRetainDuration(Clock.UNITS_PER_SEC);
        for (int r = 0; r <= rounds; r++) {
            for (int k = 0; k < keys; k++) {
                time.addAndGet(ms);
                byte[] v = new byte[val];
                v[0] = (byte) r;
                d.execute(d.trans().put("/k/" + k, v).build());
            }
        }
        final Reclaim rc = d.internal().reclaim();
        final long it0 = rc.getIterationCount(), len0 = d.getStreamLength();
        long lenHalf = 0, last = -1, itHalf = 0;
        for (int i = 0; i < calls; i++) {
            time.addAndGet(ms);
            if (M.call(d)) last = i;
            if (i == calls / 2) {
                lenHalf = d.getStreamLength();
                itHalf = rc.getIterationCount();
            }
        }
        final long len = d.getStreamLength();
        System.out.println(String.format("keys %d val %d sd %d rounds %d reserve %d budget %d: "
                + "%d calls, iterations %d (%d in the last half), wrote %d bytes, %d in the last "
                + "half; last call that wrote %d; kept %d", keys, val, sd, rounds, reserve, M.B,
                calls, rc.getIterationCount() - it0, rc.getIterationCount() - itHalf, len - len0,
                len - lenHalf, last, len - d.getFirstAvailablePos()));
        d.close();
    }
}
