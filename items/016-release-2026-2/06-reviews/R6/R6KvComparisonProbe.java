package bergdb.core;

import java.io.File;

/**
 * R6 (bergdb 016-06/R6): KvComparison.comparisonWithRestarted right after 50 commits,
 * without a sync, on a MemoryStream behind a write buffer of 1 MB and 50 ms; 20 rounds.
 */
public class R6KvComparisonProbe {
    public static void main(String[] args) throws Exception {
        File dir = new File(args[0]);
        dir.mkdirs();
        int differ = 0;
        for (int round = 0; round < 20; round++) {
            try (Db db = Db.builder().stream("main", new bergdb.stream.MemoryStream(), 1000 * 1000, 50)
                    .clock(new CoreTestClock()).noEvict().retainForever().testId().start()) {
                for (int i = 0; i < 50; i++) db.execute(db.trans().put("/k" + i, "v" + i));
                if (!KvComparison.comparisonWithRestarted(db).compare()) differ++;
            }
        }
        System.out.println("rounds that differ: " + differ + " of 20");
    }
}
