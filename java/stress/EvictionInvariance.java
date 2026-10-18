package bergdb.core;

import java.util.Set;
import java.util.TreeSet;

/**
 * Eviction invariance (bergdb item 001, WPs J2 and J3; docs/level4-alignment.md, 7): the
 * workload of RestartInvariance, run with each eviction schedule (Eviction: none; values,
 * every detachable value after every transaction; every detachable object after every
 * transaction; random), must give the same stream byte for byte (from
 * the cut, with reclaim), the same D and the same key-value checksum at every checkpoint,
 * and right answers (lookups at random times against the history), as the Lean model's
 * T-CACHE and T2-C say for every cache schedule. Also with reclaim (retain=S) and with
 * restarts (restarts=1: every N transactions, as RestartInvariance's run B).
 *
 * <p>Usage: java [-Dprop=value ...] -cp bergdb.jar:. bergdb.core.EvictionInvariance seed.
 * Properties: as RestartInvariance (n, keys, sd, maxnode, every, valsize, del, long,
 * bigtrans, empty, nodel, retain); restarts=1; evictseed (the random schedule's seed).
 * Prints a line per schedule, then EVICTION INVARIANCE OK or FAILED.</p>
 */
public class EvictionInvariance {
    public static void main(String[] args) {
        long seed = Long.parseLong(args[0]);
        boolean restarts = "1".equals(System.getProperty("restarts"));
        RestartInvariance ri = new RestartInvariance(seed);
        Set<Integer> checkpoints = new TreeSet<Integer>();
        for (int i = ri.every - 1; i < ri.n; i += ri.every) checkpoints.add(i);
        checkpoints.add(ri.n - 1);

        String[] schedules = {"none", "values", "every", "random"};
        RestartInvariance.Run[] runs = new RestartInvariance.Run[schedules.length];
        String[] evictions = new String[schedules.length];
        for (int s = 0; s < schedules.length; s++) {
            System.setProperty("evict", schedules[s]);
            long[] before = Eviction.totals();
            runs[s] = ri.run(restarts, checkpoints);
            long[] after = Eviction.totals();
            evictions[s] = "eviction " + schedules[s] + ": " + (after[0] - before[0])
                    + " slots unswizzled, " + (after[1] - before[1]) + " objects released";
        }
        System.setProperty("evict", "none");

        System.out.println("seed=" + seed + " n=" + ri.n + " keys=" + ri.keyCount + " sd="
                + ri.startupDistance + " maxnode=" + ri.maxNode + " retain=" + ri.retain
                + " restarts=" + (restarts ? "every " + ri.every : "none"));
        int bad = 0;
        RestartInvariance.Run a = runs[0];
        for (int s = 0; s < schedules.length; s++) {
            RestartInvariance.Run r = runs[s];
            StringBuilder line = new StringBuilder("SCHEDULE " + schedules[s] + ": ");
            boolean ok = true;
            if (r.startupFailure != null) {
                line.append("STARTUP FAILED: ").append(r.startupFailure);
                ok = false;
            } else {
                long diff = RestartInvariance.firstDiff(a.stream, r.stream);
                boolean same = diff < 0 && a.stream.getLength() == r.stream.getLength();
                line.append("stream ").append(same ? "identical" : "DIFFERS at " + diff);
                ok &= same;
                int ts = 0, kv = 0;
                for (int i : checkpoints) {
                    if (!a.transSeqSums.get(i).equals(r.transSeqSums.get(i))) ts++;
                    if (!a.dbSums.get(i).equals(r.dbSums.get(i))) kv++;
                }
                line.append("; TRANSSEQ ").append(ts).append(" of ").append(checkpoints.size())
                        .append(" checkpoints differ; KV CHECKSUM ").append(kv).append(" differ");
                line.append("; IDENTITY ").append(r.identity.size()).append(" violate; LOOKUP ")
                        .append(r.lookups.size()).append(" violate");
                ok &= ts == 0 && kv == 0 && r.identity.isEmpty() && r.lookups.isEmpty();
                if (!r.lookups.isEmpty()) {
                    line.append(" (first: ").append(r.lookups.values().iterator().next()).append(")");
                }
            }
            line.append("; ").append(evictions[s]);
            System.out.println(line);
            if (!ok) bad++;
        }
        if (Audit.EVERY > 0) System.out.println(Audit.summary());
        System.out.println(bad == 0 ? "EVICTION INVARIANCE OK" : "EVICTION INVARIANCE FAILED");
        if (bad != 0) System.exit(1);
    }
}
