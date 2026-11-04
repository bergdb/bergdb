package bergdb.core;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import bergdb.common.StringUtil;
import bergdb.storage.RecoverableStream;
import bergdb.stream.CutStream;

/**
 * R6's crash probe of setStartupDistance's record (bergdb 016-06/R6): a database at 1 MB
 * with 400 transactions, then setStartupDistance(500,000), whose record of 200 kB holds a
 * meta block, then 100 transactions. The stream is cut at about 230 positions in and
 * around that record (every 997 bytes, its meta block's position -1 to +129, its end
 * -1 to +1) and near the end; each copy is started, every key checked against the state
 * after the last transaction whose last byte is before the cut, 20 transactions run, the
 * database restarted and checked again. Prints failures and a summary.
 */
public class R6DecreaseCrashProbe {
    static final int KEYS = 60;
    public static void main(String[] args) throws Exception {
        CutStream stream = new CutStream();
        CoreTestClock clock = new CoreTestClock();
        List<Long> lastPos = new ArrayList<Long>();
        List<Map<String, String>> states = new ArrayList<Map<String, String>>();
        Map<String, String> state = new HashMap<String, String>();
        long dTpos, dLast;
        long time = 10;
        java.util.Random r = new java.util.Random(6);
        try (Db db = Db.builder().testSetup(stream).clock(clock)
                .startupDistance(1000000).retainForever().start()) {
            for (int i = 0; i < 400; i++) {
                put(db, clock, time++, r, state, lastPos, states);
            }
            long before = db.getStreamLength();
            clock.setTime(time++);
            db.setStartupDistance(500000);
            dTpos = before;
            dLast = db.getStreamLength() - 1;
            lastPos.add(dLast);
            states.add(new HashMap<String, String>(state));
            for (int i = 0; i < 100; i++) {
                put(db, clock, time++, r, state, lastPos, states);
            }
        }
        List<Long> cuts = new ArrayList<Long>();
        for (long p = dTpos - 8; p <= dLast + 2; p += 997) cuts.add(p);
        long meta = (dTpos / RecoverableStream.META_BLOCK_DISTANCE + 1) 
                * RecoverableStream.META_BLOCK_DISTANCE;
        for (int o : new int[] {-1, 0, 1, 64, 127, 128, 129}) cuts.add(meta + o);
        for (int o : new int[] {-1, 0, 1, 2}) cuts.add(dLast + o);
        for (int i = 0; i < 5; i++) cuts.add(stream.getLength() - 1 - 37 * i);
        int failures = 0, newSd = 0, oldSd = 0;
        for (long cut : cuts) {
            CutStream copy = stream.copy();
            copy.truncate(cut);
            int k = -1;
            for (int i = 0; i < lastPos.size(); i++) if (lastPos.get(i) < cut) k = i;
            Map<String, String> expected = k < 0 ? new HashMap<String, String>() : states.get(k);
            try {
                try (Db db = Db.builder().testSetup(copy).clock(clock)
                        .startupDistance(1000000).retainForever().start()) {
                    String f = check(db, expected);
                    if (db.getStartupDistance() == 500000) newSd++; else oldSd++;
                    if (f != null) { failures++; System.out.println("cut " + cut + ": " + f); }
                    Map<String, String> after = new HashMap<String, String>(expected);
                    for (int i = 0; i < 20; i++) {
                        put(db, clock, time++, r, after, new ArrayList<Long>(), 
                                new ArrayList<Map<String, String>>());
                    }
                    expected = after;
                }
                try (Db db = Db.builder().testSetup(copy).clock(clock)
                        .startupDistance(1000000).retainForever().start()) {
                    String f = check(db, expected);
                    if (f != null) { failures++; System.out.println("cut " + cut + ", again: " + f); }
                }
            } catch (RuntimeException | AssertionError e) {
                failures++;
                System.out.println("cut " + cut + ": " + e);
            }
        }
        System.out.println("record of setStartupDistance at " + dTpos + " to " + dLast 
                + ", meta block at " + meta + "; " + cuts.size() + " cuts, " + failures 
                + " failures; setting after the start: 500,000 in " + newSd + ", 1,000,000 in "
                + oldSd);
    }

    static void put(Db db, CoreTestClock clock, long time, java.util.Random r,
            Map<String, String> state, List<Long> lastPos, List<Map<String, String>> states) {
        clock.setTime(time);
        Trans.Builder b = db.trans();
        Map<String, String> ops = new HashMap<String, String>();
        int n = 1 + r.nextInt(3);
        for (int j = 0; j < n; j++) {
            String key = "/k/" + r.nextInt(KEYS);
            String v = r.nextInt(5) == 0 ? null : "v" + time + "-" + j;
            ops.put(key, v);
        }
        for (Map.Entry<String, String> e : ops.entrySet()) {
            if (e.getValue() == null) b.delete(e.getKey()); else b.put(e.getKey(), e.getValue());
        }
        Trans t = b.build();
        db.execute(t);
        for (Map.Entry<String, String> e : ops.entrySet()) {
            if (e.getValue() == null) state.remove(e.getKey()); else state.put(e.getKey(), e.getValue());
        }
        lastPos.add(t.lastPos);
        states.add(new HashMap<String, String>(state));
    }

    static String check(Db db, Map<String, String> expected) {
        for (int i = 0; i < KEYS; i++) {
            String key = "/k/" + i;
            byte[] v = DbUtil.get(db, Long.MAX_VALUE, key);
            String actual = v == null ? null : StringUtil.toString(v);
            String e = expected.get(key);
            if (e == null ? actual != null : !e.equals(actual)) {
                return key + " is " + actual + ", expected " + e;
            }
        }
        return null;
    }
}
