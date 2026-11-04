package bergdb.core;

import bergdb.stream.MemoryStream;

/**
 * R6 (bergdb 016-06/R6): the same stream with and without a restart (T2), for transactions
 * that mix deletes of keys that do not exist with puts that split nodes, and for
 * setStartupDistance; node size 8. One run commits 600 transactions; the other stops after
 * each 50 and starts again on a copy. Prints the first differing byte, or "SAME".
 */
public class R6RestartSameStreamProbe {
    public static void main(String[] args) throws Exception {
        for (int sd : new int[] {1000, 30000, 1000000}) {
            MemoryStream a = run(sd, false), b = run(sd, true);
            long n = Math.min(a.getLength(), b.getLength());
            byte[] x = new byte[(int) n], y = new byte[(int) n];
            a.read(0, x, 0, (int) n);
            b.read(0, y, 0, (int) n);
            long diff = -1;
            for (int i = 0; i < n && diff < 0; i++) if (x[i] != y[i]) diff = i;
            System.out.println("sd " + sd + ": lengths " + a.getLength() + ", " + b.getLength()
                    + (diff < 0 && a.getLength() == b.getLength() ? ", SAME" : ", first difference at " + diff));
        }
    }

    static MemoryStream run(int sd, boolean restarts) {
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        java.util.Random r = new java.util.Random(sd);
        long time = 10;
        int done = 0;
        while (done < 600) {
            try (Db db = Db.builder().testSetup(stream).clock(clock).maxNodeSize8()
                    .startupDistance(sd).start()) {
                int stop = restarts ? done + 50 : 600;
                for (; done < stop; done++) {
                    clock.setTime(time++);
                    if (done == 300) {
                        db.setStartupDistance(sd == 1000000 ? 500000 : 400000);
                        continue;
                    }
                    Trans.Builder t = db.trans();
                    int n = 1 + r.nextInt(30);
                    for (int j = 0; j < n; j++) {
                        int k = r.nextInt(3000);
                        if (r.nextInt(3) == 0) t.delete("/k/" + k + "x");   // does not exist
                        else if (r.nextInt(5) == 0) t.delete("/k/" + k);
                        else t.put("/k/" + k, "v" + time);
                    }
                    db.execute(t.build());
                }
            }
            stream = stream.copy();
        }
        return stream;
    }
}
