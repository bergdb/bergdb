package bergdb.core;

import java.util.*;

import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.TransactionInfo;
import bergdb.pubimp.DatabaseImp;

/**
 * bergdb 031-06, a part of SafetyProbe (Codex's third test): the Pub API's
 * Connection.transactionInfo() on a Core Db with a test clock, through reclaim's copies in
 * commits' and parts' records, before and after cuts and restarts: for every key whose put
 * is still available, the time that its put returned and its one KV.
 */
public class PubInfoProbe {
    /** DatabaseImp.createAndStart(db), which is not public (bergdb.pubimp is sealed). */
    static Database start(Db db) throws Exception {
        java.lang.reflect.Method m = DatabaseImp.class.getDeclaredMethod("createAndStart", Db.class);
        m.setAccessible(true);
        return (Database) m.invoke(null, db);
    }

    /** The Pub API's transactionInfo() on a Core Db with a test clock, with cuts and restarts. */
    public static void run(long seed, int n, int SD, long RESERVE, int NODE) throws Exception {
        final long SEC = bergdb.pub.util.Clock.UNITS_PER_SEC;
        Random r = new Random(seed + 1000);
        bergdb.pub.TestClock pc = new bergdb.pub.TestClock();
        long t = SEC;
        pc.setTime(bergdb.pub.Time.units(t));
        bergdb.stream.CutStream s = new bergdb.stream.CutStream();
        Db db = TestNodeSize.builder(NODE == 0 ? 30 : NODE).testSetup(s).clock(pc).reclaimStepReserve(RESERVE).build();
        Database d = start(db);
        db.setStartupDistance(SD);
        d.setRetainDuration(bergdb.pub.Duration.seconds(1));
        Map<String, Long> putTime = new TreeMap<>();
        long infos = 0, cuts = 0, last = 0;
        try {
            for (int i = 0; i < n; i++) {
                t += SEC / 20; pc.setTime(bergdb.pub.Time.units(t));
                Connection c = d.connection();
                String k = (r.nextInt(3) == 0 ? "/cold/" + r.nextInt(100) : "/hot/" + r.nextInt(20)) + ".txt";
                if (!putTime.containsKey(k) || k.startsWith("/hot/")) {
                    StringBuilder v = new StringBuilder("v" + i);
                    for (int j = r.nextInt(800); j > 0; j--) v.append((char) ('a' + r.nextInt(26)));
                    long tt = c.put(k, v.toString()).getTime().units();
                    putTime.put(k, tt);
                }
                if (i % 97 == 96) {
                    d.close();      // close() waits for the storage; stop() would not
                    s = s.copy();
                    db = TestNodeSize.builder(NODE == 0 ? 30 : NODE).testSetup(s).clock(pc).reclaimStepReserve(RESERVE).build();
                    d = start(db);
                    c = d.connection();
                }
                if (db.getFirstAvailablePos() != last) { cuts++; last = db.getFirstAvailablePos(); }
                if (i % 25 == 24 || i == n - 1) {
                    long first = d.getFirstAvailableLookupTime().units();
                    for (Map.Entry<String, Long> e : putTime.entrySet()) {
                        c.get(e.getKey(), String.class);
                        if (e.getValue() < first) continue;     // refused: before the first time
                        TransactionInfo info = c.transactionInfo();
                        infos++;
                        if (info.time().units() != e.getValue()) throw new AssertionError("pub: "
                                + e.getKey() + ": transactionInfo at " + info.time().units()
                                + ", put at " + e.getValue());
                        boolean has = false;
                        for (bergdb.pub.Kv<byte[]> kv : info.kvs()) has |= kv.key().equals(e.getKey());
                        if (!has || info.kvs().size() != 1) throw new AssertionError("pub: " + e.getKey()
                                + ": the KVs " + info.kvs().size() + ", the key among them " + has);
                    }
                }
            }
        } finally {
            d.close();
        }
        System.out.println("pub: " + n + " actions, " + infos + " transactionInfo() checked, "
                + cuts + " cuts seen: OK");
    }
}
