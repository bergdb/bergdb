package bergdb.core;

import bergdb.pub.util.Clock;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.stream.CutStream;

/** A fixed live set moving below a permanent maximum key. */
public final class ReclaimBeforeEnd {
    static String key(int n) { return String.format("/m/%09d", n); }
    static String end(Object it) {
        try {
            java.lang.reflect.Field f = it.getClass().getDeclaredField("endKey");
            f.setAccessible(true);
            return Keys.toString((long[]) f.get(it));
        } catch (ReflectiveOperationException e) { return "start-snapshot"; }
    }
    public static void main(String[] args) {
        int rounds = args.length == 0 ? 1200 : Integer.parseInt(args[0]);
        CoreTestClock clock = new CoreTestClock();
        long now = 10 * Clock.UNITS_PER_SEC;
        clock.setTime(now);
        Db db = Db.builder().testSetup(new CutStream()).clock(clock)
                .startupDistance(100000).start();
        Reclaim rc = db.internal().reclaim();
        Reclaim.Stats stats = rc.enableStats();
        byte[] value = new byte[100];
        final int live = 1000, batch = 200;
        db.execute(db.trans().put("/z", "sentinel").build());
        for (int i = 0; i < live; i += batch) {
            clock.setTime(now += 10000);
            Trans.Builder b = db.trans();
            for (int j = i; j < i + batch; j++) b.put(key(j), value);
            db.execute(b.build());
        }
        db.setRetainDuration(Clock.UNITS_PER_SEC);
        int next = live;
        long start = 0;
        for (int i = 0; i < rounds; i++) {
            clock.setTime(now += 10000);
            Trans.Builder b = db.trans();
            for (int j = 0; j < batch; j++, next++) {
                b.delete(key(next - live));
                b.put(key(next), value);
            }
            db.execute(b.build());
            if (i == 0) start = rc.currentIteration().tStart;
            if ((i+1) % 300 == 0) {
                Reclaim.IterationInfo it = rc.currentIteration();
                System.out.println("round=" + (i+1) + " completed=" + rc.getIterationCount()
                        + " first=" + rc.getFirstAvailablePos() + " bytes=" + db.getStreamLength()
                        + " sameIteration=" + (it != null && it.tStart == start)
                        + " cursor=" + (it == null ? "none" : Keys.toString(it.lastKey))
                        + " end=" + (it == null ? "none" : end(it))
                        + " steps=" + stats.iterations.get(0).steps);
            }
        }
        GetMany g = db.newGetMany();
        g.stopCondition = new GetMany.DontStop();
        db.getMany(g);
        System.out.println("liveKVs=" + g.result.size() + " userKVs="
                + g.result.stream().filter(k -> !Keys.toString(k.key).startsWith("/#i/")).count());
        db.close();
    }
}
