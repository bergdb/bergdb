import bergdb.pub.*;
import bergdb.pub.util.*;
import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.*;

/**
 * RwReplace (031-02, e11). Key replace in rw() transactions that conflict and run again:
 * threads increment shared counters, and each increment also puts the value it wrote at
 * "/log/cN/${transactionTime}.txt", with the connection's key replace on. The time in the
 * key must be the time of the run that committed (RwEnvironment.put()), so that, listed in
 * key order, which is the order of the times, the log of each counter holds 1, 2, 3, ...
 * with no gap and no repeat, each entry's time equal to Transaction.getTime() of the rw()
 * that returned it, and readable at that time with the counter's value then.
 *
 * Usage: java RwReplace DIR|mem SEED SECONDS THREADS
 */
public class RwReplace {
    static void fail(String m) {
        System.out.println("RWREPLACE FAILED: " + m);
        System.out.flush();
        System.exit(1);
    }

    static final int COUNTERS = 3;

    public static void main(String[] args) throws Exception {
        String dir = args[0];
        long seed = Long.parseLong(args[1]);
        int seconds = Integer.parseInt(args[2]);
        int threads = Integer.parseInt(args[3]);
        System.out.println("RwReplace seed " + seed + " seconds " + seconds + " threads " + threads);
        Database db = (dir.equals("mem") ? Factory.database().memory() : Factory.database().create(dir)).start();
        // counter -> (value -> time of the rw() that wrote it)
        List<ConcurrentHashMap<Long, Long>> written = new ArrayList<>();
        for (int i = 0; i < COUNTERS; i++) written.add(new ConcurrentHashMap<>());
        AtomicLong runs = new AtomicLong(), commits = new AtomicLong();
        long end = System.currentTimeMillis() + seconds * 1000L;
        List<Thread> ts = new ArrayList<>();
        for (int t = 0; t < threads; t++) {
            final long s = seed * 100 + t;
            Thread th = new Thread(() -> {
                Random r = new Random(s);
                Connection c = db.connection();
                c.setEnableKeyReplace(true);
                while (System.currentTimeMillis() < end) {
                    int n = r.nextInt(COUNTERS);
                    int sleep = r.nextInt(4);
                    Transaction tr = c.rw(env -> {
                        runs.incrementAndGet();
                        String v = env.get("/c/c" + n + ".txt", String.class);
                        long x = v == null ? 1 : Long.parseLong(v) + 1;
                        if (sleep > 0) { try { Thread.sleep(sleep); } catch (InterruptedException e) { throw new RuntimeException(e); } }
                        env.put("/c/c" + n + ".txt", Long.toString(x));
                        env.put("/log/c" + n + "/${transactionTime}.txt", Long.toString(x));
                        env.setOutput("x", x);
                    });
                    long x = tr.getOutput("x", Long.class);
                    if (written.get(n).put(x, tr.getTime().units()) != null) fail("counter " + n + " value " + x + " committed twice");
                    commits.incrementAndGet();
                }
            });
            th.start();
            ts.add(th);
        }
        for (Thread th : ts) th.join();
        Connection c = db.connection();
        Connection old = db.newConnection();
        for (int n = 0; n < COUNTERS; n++) {
            long expect = 1;
            for (Kv<String> kv : c.usePrimary(String.class).dir("/log/c" + n + "/").kvs()) {
                long x = Long.parseLong(kv.value());
                if (x != expect) fail("counter " + n + ": the log's entry " + kv.key() + " holds " + x + ", expected " + expect);
                long tt = Long.parseLong(kv.key().substring(kv.key().lastIndexOf('/') + 1, kv.key().length() - 4));
                Long t = written.get(n).get(x);
                if (t == null || t != tt) fail("counter " + n + ": value " + x + " logged at " + tt + ", its rw() returned "
                        + "the time " + t);
                old.setLookupTime(Time.units(tt));
                if (!Long.toString(x).equals(old.get("/c/c" + n + ".txt", String.class))) fail("counter " + n + " at " + tt
                        + " is not " + x);
                old.setLookupTime(Time.units(tt - 1));
                String before = old.get("/c/c" + n + ".txt", String.class);
                if (!(x == 1 ? before == null : Long.toString(x - 1).equals(before))) fail("counter " + n + " just before "
                        + tt + " is " + before + ", not " + (x - 1));
                expect++;
            }
            long last = Long.parseLong(c.get("/c/c" + n + ".txt", String.class));
            if (last != expect - 1 || written.get(n).size() != last) fail("counter " + n + " is " + last + ", the log has "
                    + (expect - 1) + ", committed " + written.get(n).size());
        }
        db.close();
        System.out.println("commits " + commits + ", action runs " + runs + " (" + (runs.get() - commits.get()) + " again)");
        System.out.println("RWREPLACE OK");
    }
}
