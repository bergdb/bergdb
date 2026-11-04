package bergdb.core;

/**
 * R6's check of T3 for Java's take (bergdb 016-06/R6; levels.md 5, "Limits": the section
 * without its last record stays below twice the startup distance): after every commit,
 * TransSeq.span(), the span from T(s+1) to T(i), which is Lean's Stream.span after T(i),
 * must be below 2 sd. Random transactions of 1 to 3 puts or deletes, now and then 40, over
 * 2,000 keys, values of 0 to 300 bytes; restarts now and then.
 */
public class R6SpanProbe {
    public static void main(String[] args) throws Exception {
        for (int sd : new int[] {100, 2000, 20000}) {
            for (int node : new int[] {8, 30}) {
                run(sd, node, 7 + sd + node);
            }
        }
    }

    static void run(int sd, int node, long seed) {
        java.util.Random r = new java.util.Random(seed);
        bergdb.stream.MemoryStream stream = new bergdb.stream.MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        long time = 10;
        long maxSpan = 0;
        int commits = 0, over = 0;
        for (int run = 0; run < 4; run++) {
            DbBuilder b = Db.builder().testSetup(stream).clock(clock).startupDistance(sd);
            if (node == 8) b.maxNodeSize8(); else b.maxNodeSize30();
            try (Db db = b.start()) {
                for (int i = 0; i < 1500; i++) {
                    clock.setTime(time++);
                    Trans.Builder t = db.trans();
                    int n = r.nextInt(20) == 0 ? 40 : 1 + r.nextInt(3);
                    for (int j = 0; j < n; j++) {
                        String key = "/k/" + r.nextInt(2000);
                        if (r.nextInt(6) == 0) t.delete(key);
                        else t.put(key, new byte[r.nextInt(300)]);
                    }
                    db.execute(t.build());
                    commits++;
                    long span = db.internal().transSeq().span();
                    maxSpan = Math.max(maxSpan, span);
                    if (span >= 2L * db.getStartupDistance()) {
                        if (over++ < 3) System.out.println("sd " + sd + ", node " + node 
                                + ", commit " + commits + ": span " + span + " >= 2 sd");
                    }
                }
            }
            stream = stream.copy();
        }
        System.out.println("sd " + sd + ", node " + node + ": " + commits + " commits, max span "
                + maxSpan + " (2 sd = " + 2L * sd + "), " + over + " over");
    }
}
