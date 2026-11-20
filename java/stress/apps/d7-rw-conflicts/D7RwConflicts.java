import bergdb.pub.*;
import bergdb.pub.util.IllegalDbStateException;
import java.nio.file.*;
import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.*;

/** Functional controlled-conflict checks. Usage: D7RwConflicts DIR SEED [rounds]. */
public final class D7RwConflicts {
    public static class Data { public long value; public Data() { } Data(long n) { value = n; } }
    public static class Throwing {
        public long value; static volatile int mode;
        public Throwing() {
            if (mode == 1) throw new IllegalArgumentException("constructor refusal");
            if (mode == 2) throw new AssertionError("constructor error");
        }
    }
    final Map<String, String> oracle = new HashMap<>();
    final ExecutorService threads = Executors.newFixedThreadPool(4);
    long assertions, retries, pairs;
    static void check(boolean ok, String m) { if (!ok) throw new IllegalStateException(m); }
    static void await(CountDownLatch latch) {
        try { check(latch.await(30, TimeUnit.SECONDS), "latch hang guard"); }
        catch (InterruptedException e) { throw new IllegalStateException(e); }
    }
    static void barrier(CyclicBarrier b) {
        try { b.await(30, TimeUnit.SECONDS); } catch (Exception e) { throw new IllegalStateException(e); }
    }
    void verify(Database db) {
        Connection c = db.newConnection(); c.freezeLookupTime();
        Map<String, String> got = new HashMap<>();
        for (Kv<String> e : c.usePrimary(String.class).dir("/conflicts/").kvs()) check(got.put(e.key(), e.value()) == null, "duplicate scan key");
        check(got.equals(oracle), "committed state differs from model");
        for (var e : oracle.entrySet()) {
            check(e.getValue().equals(c.get(e.getKey(), String.class)) && c.exists(e.getKey()), "point read differs " + e.getKey()); assertions++;
        }
    }
    void firstRead(Database db, int round, boolean writeBeforeRead) throws Exception {
        Connection c = db.connection(); String k = "/conflicts/late" + round + ".txt", output = "/conflicts/observed" + round + ".txt";
        c.put(k, "old"); oracle.put(k, "old");
        CountDownLatch action = new CountDownLatch(1), committed = new CountDownLatch(1);
        Future<Transaction> f = threads.submit(() -> db.connection().rw(env -> {
            if (writeBeforeRead) env.put(output, "before first read");
            action.countDown(); await(committed);
            String read = env.get(k, String.class); env.setOutput("read", read); env.put(output, read);
        }));
        await(action); c.put(k, "new"); oracle.put(k, "new"); committed.countDown();
        Transaction t = f.get(30, TimeUnit.SECONDS);
        check(t.getOutput("read", String.class).equals("new"), "first read used state from before the first read");
        oracle.put(output, "new"); assertions++;
    }
    void missingConflict(Database db, int round) throws Exception {
        String missing = "/conflicts/missing" + round + ".txt", out = "/conflicts/result" + round + ".txt";
        CountDownLatch read = new CountDownLatch(1), changed = new CountDownLatch(1);
        AtomicInteger attempts = new AtomicInteger(); AtomicReference<RwEnvironment> old = new AtomicReference<>();
        Future<Transaction> f = threads.submit(() -> db.connection().rw(env -> {
            int attempt = attempts.incrementAndGet(); boolean present = env.exists(missing);
            if (attempt == 1) {
                old.set(env); env.setOutput("obsolete", "first-attempt"); read.countDown(); await(changed);
            } else {
                boolean closed = false; try { old.get().exists(missing); } catch (IllegalStateException good) { closed = true; }
                check(closed, "earlier attempt environment reopened");
            }
            env.put(out, present ? "present" : "absent"); env.setOutput("present", present);
        }));
        await(read); db.connection().put(missing, "written"); oracle.put(missing, "written"); changed.countDown();
        Transaction t = f.get(30, TimeUnit.SECONDS);
        check(attempts.get() >= 2 && t.getOutput("present", Boolean.class), "absent read did not conflict with insertion");
        check(t.getOutput("obsolete", String.class) == null, "outputs leaked from refused attempt");
        oracle.put(out, "present"); retries += attempts.get() - 1; assertions += 3;
    }
    void snapshot(Database db, int round) throws Exception {
        String a = "/conflicts/a" + round + ".txt", b = "/conflicts/b" + round + ".txt", out = "/conflicts/snapshot" + round + ".txt";
        db.connection().w().put(a, "0").put(b, "0").execute(); oracle.put(a, "0"); oracle.put(b, "0");
        CountDownLatch first = new CountDownLatch(1), changed = new CountDownLatch(1); AtomicInteger attempts = new AtomicInteger();
        Future<Transaction> f = threads.submit(() -> db.connection().rw(env -> {
            int attempt = attempts.incrementAndGet(); String x = env.get(a, String.class);
            if (attempt == 1) { first.countDown(); await(changed); }
            String y = env.get(b, String.class);
            check(x.equals(y), "RW saw half of another transaction");
            env.put(out, x); env.setOutput("read", x);
        }));
        await(first); db.connection().w().put(a, "1").put(b, "1").execute();
        oracle.put(a, "1"); oracle.put(b, "1"); changed.countDown();
        Transaction t = f.get(30, TimeUnit.SECONDS);
        check(t.getOutput("read", String.class).equals("1") && attempts.get() >= 2, "snapshot conflict was not rerun");
        oracle.put(out, "1"); retries += attempts.get() - 1; assertions += attempts.get();
    }
    void skew(Database db, int round) throws Exception {
        String left = "/conflicts/left" + round + ".txt", right = "/conflicts/right" + round + ".txt";
        CyclicBarrier together = new CyclicBarrier(2); AtomicInteger la = new AtomicInteger(), ra = new AtomicInteger();
        Future<Transaction> l = threads.submit(() -> db.connection().rw(env -> {
            int attempt = la.incrementAndGet(); boolean other = env.exists(right);
            if (attempt == 1) barrier(together);
            if (!other) env.put(left, "chosen"); env.setOutput("chosen", !other);
        }));
        Future<Transaction> r = threads.submit(() -> db.connection().rw(env -> {
            int attempt = ra.incrementAndGet(); boolean other = env.exists(left);
            if (attempt == 1) barrier(together);
            if (!other) env.put(right, "chosen"); env.setOutput("chosen", !other);
        }));
        Transaction lt = l.get(30, TimeUnit.SECONDS), rt = r.get(30, TimeUnit.SECONDS);
        boolean lc = lt.getOutput("chosen", Boolean.class), rc = rt.getOutput("chosen", Boolean.class);
        check(lc != rc, "write skew: both or neither chose");
        check((lt.getTime().units() < rt.getTime().units()) == lc, "decision not consistent with commit order");
        oracle.put(lc ? left : right, "chosen"); retries += la.get() + ra.get() - 2; pairs++; assertions += 2;
    }
    void constructors(Database db) {
        Connection c = db.connection(); c.put("/objects/data", new Data(123));
        for (int mode : new int[]{1, 2}) {
            Throwing.mode = mode; boolean refused = false;
            try { c.get("/objects/data", Throwing.class); }
            catch (ObjectCreationException e) {
                refused = true; check(mode == 1 ? e.getCause() instanceof IllegalArgumentException : e.getCause() instanceof AssertionError, "constructor cause lost");
            }
            check(refused, "constructor failure not reported");
            check(c.get("/objects/data", Data.class).value == 123, "constructor failure failed database");
            c.put("/conflicts/after-constructor" + mode + ".txt", "works"); oracle.put("/conflicts/after-constructor" + mode + ".txt", "works");
            assertions += 3;
        }
        Throwing.mode = 0; check(c.get("/objects/data", Throwing.class).value == 123, "constructor mode reset failed");
    }
    void interrupts(Database db) {
        Connection c = db.connection();
        Thread.currentThread().interrupt();
        try {
            c.put("/conflicts/interrupted.txt", "committed"); oracle.put("/conflicts/interrupted.txt", "committed");
            check(Thread.currentThread().isInterrupted(), "put cleared interrupt");
            check(c.get("/conflicts/interrupted.txt", String.class).equals("committed"), "interrupted read refused");
            check(Thread.currentThread().isInterrupted(), "get cleared interrupt");
            c.rw(env -> { check(env.get("/conflicts/interrupted.txt", String.class).equals("committed"), "interrupted RW read refused"); env.put("/conflicts/interrupted-rw.txt", "committed"); });
            oracle.put("/conflicts/interrupted-rw.txt", "committed");
            check(Thread.currentThread().isInterrupted(), "RW cleared interrupt"); assertions += 4;
        } finally { Thread.interrupted(); }
    }
    void stoppedAction(Database db) throws Exception {
        CountDownLatch entered = new CountDownLatch(1), stopped = new CountDownLatch(1);
        Future<?> f = threads.submit(() -> db.connection().rw(env -> {
            env.put("/conflicts/stopped-poison.txt", "must not commit"); entered.countDown(); await(stopped);
        }));
        await(entered); db.stop(); stopped.countDown(); boolean refused = false;
        try { f.get(30, TimeUnit.SECONDS); }
        catch (ExecutionException e) { check(e.getCause() instanceof IllegalDbStateException, "wrong stop refusal " + e.getCause()); refused = true; }
        check(refused, "action committed after stop"); db.close(); assertions++;
    }
    public static void main(String[] args) throws Exception {
        String path = args[0]; long seed = Long.parseLong(args[1]); int rounds = args.length > 2 ? Integer.parseInt(args[2]) : 80;
        check(!Files.exists(Path.of(path)), "use a fresh directory");
        System.out.println("Kind: functional; D7RwConflicts seed=" + seed + " rounds=" + rounds);
        D7RwConflicts app = new D7RwConflicts(); Random random = new Random(seed);
        try {
            try (Database db = Factory.database().create(path).cacheSizeInMb(48).start()) {
                for (int round = 0; round < rounds; round++) {
                    app.firstRead(db, round, random.nextBoolean()); app.missingConflict(db, round); app.snapshot(db, round); app.skew(db, round);
                    if (round % 13 == 0) app.verify(db);
                }
                app.constructors(db); app.interrupts(db); app.verify(db); db.sync(); app.stoppedAction(db);
            }
            try (Database db = Factory.database().open(path).cacheSizeInMb(48).start()) {
                app.verify(db); check(!db.connection().exists("/conflicts/stopped-poison.txt"), "refused stopped action persisted");
            }
        } finally { app.threads.shutdownNow(); }
        System.out.println("OK D7RwConflicts pairs=" + app.pairs + " retries=" + app.retries + " assertions=" + app.assertions + " restart=checked");
    }
}
