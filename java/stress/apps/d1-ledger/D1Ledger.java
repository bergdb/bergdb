import bergdb.pub.*;
import java.nio.file.*;
import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.*;

/** Functional consistency checks. Usage: D1Ledger DIR SEED [epochs] [per-writer]. */
public final class D1Ledger {
    static final int ACCOUNTS = 12, WRITERS = 4, READERS = 2;
    static final long INITIAL = 1000000;
    record Move(int from, int to, long amount, int id, long beforeFrom, long beforeTo) {}
    record Commit(long time, Move move) {}
    record View(long time, long[] balances, NavigableMap<String, String> journal) {}
    static String account(int n) { return "/accounts/a" + n; }
    static String journal(long t) { return "/journal/" + String.format(Locale.ROOT, "%018d", t) + ".txt"; }
    static String text(Move m) { return m.id + ":" + m.from + ":" + m.to + ":" + m.amount; }
    static void check(boolean ok, String message) { if (!ok) throw new IllegalStateException(message); }
    static void verify(Database db, View v) {
        Connection c = db.newConnection();
        c.setLookupTime(Time.units(v.time));
        long sum = 0;
        for (int i = 0; i < ACCOUNTS; i++) {
            Long got = c.get(account(i), Long.class);
            check(got != null && got == v.balances[i], "balance at " + v.time + " account " + i
                    + ": expected " + v.balances[i] + ", got " + got);
            check(c.exists(account(i)), "exists false " + i);
            sum += got;
        }
        check(sum == INITIAL * ACCOUNTS, "money was created or lost");
        NavigableMap<String, String> got = new TreeMap<>();
        for (Kv<String> e : c.usePrimary(String.class).dir("/journal/").kvs()) {
            check(got.put(e.key(), e.value()) == null, "duplicate journal key");
        }
        check(got.equals(v.journal), "journal at " + v.time + ": expected " + v.journal.size()
                + " entries, got " + got.size());
    }
    public static void main(String[] args) throws Exception {
        String path = args[0]; long seed = Long.parseLong(args[1]);
        int epochs = args.length > 2 ? Integer.parseInt(args[2]) : 6;
        int count = args.length > 3 ? Integer.parseInt(args[3]) : 200;
        check(!Files.exists(Path.of(path)), "use a fresh directory");
        System.out.println("Kind: functional; D1Ledger seed=" + seed + " epochs=" + epochs + " perWriter=" + count);
        List<Commit> commits = Collections.synchronizedList(new ArrayList<>());
        List<View> views = new ArrayList<>();
        long[] oracle = new long[ACCOUNTS]; Arrays.fill(oracle, INITIAL);
        NavigableMap<String, String> journal = new TreeMap<>();
        AtomicReference<Throwable> failure = new AtomicReference<>();
        ExecutorService pool = Executors.newFixedThreadPool(WRITERS + READERS);
        try (Database db = Factory.database().create(path).cacheSizeInMb(64).start()) {
            WBuilder initial = db.connection().w();
            for (int a = 0; a < ACCOUNTS; a++) initial.put(account(a), INITIAL);
            long first = initial.execute().getTime().units();
            views.add(new View(first, oracle.clone(), new TreeMap<>(journal)));
            for (int epoch = 0; epoch < epochs; epoch++) {
                int ep = epoch;
                List<View> published = List.copyOf(views);
                CountDownLatch start = new CountDownLatch(1);
                List<Future<?>> futures = new ArrayList<>();
                for (int w = 0; w < WRITERS; w++) {
                    int worker = w;
                    futures.add(pool.submit(() -> {
                        try {
                            start.await();
                            Random random = new Random(seed ^ (ep * 1009L + worker * 65537L));
                            Connection c = db.connection(); c.setEnableKeyReplace(true);
                            for (int n = 0; n < count && failure.get() == null; n++) {
                                int from = random.nextInt(ACCOUNTS), other = random.nextInt(ACCOUNTS - 1);
                                int to = other >= from ? other + 1 : other;
                                long amount = 1 + random.nextInt(100);
                                int id = (ep * WRITERS + worker) * count + n;
                                Time before = c.currentTime();
                                Transaction transaction = c.rw(env -> {
                                    long a = env.get(account(from), Long.class), b = env.get(account(to), Long.class);
                                    env.put(account(from), -999L);
                                    env.delete(account(to));
                                    check(env.get(account(from), Long.class) == a, "RW saw its own write");
                                    check(env.get(account(to), Long.class) == b, "RW saw its own delete");
                                    env.put(account(from), a - amount); env.put(account(to), b + amount);
                                    Move move = new Move(from, to, amount, id, a, b);
                                    env.put("/journal/${transactionTime}.txt", text(move));
                                    env.setOutput("move", move);
                                });
                                long time = transaction.getTime().units();
                                check(time > before.units(), "currentTime not before transaction");
                                commits.add(new Commit(time, transaction.getOutput("move", Move.class)));
                            }
                        } catch (Throwable t) { failure.compareAndSet(null, t); }
                    }));
                }
                for (int r = 0; r < READERS; r++) {
                    int reader = r;
                    futures.add(pool.submit(() -> {
                        try {
                            start.await(); Random random = new Random(seed + ep * 101L + reader);
                            for (int n = 0; n < 25 && failure.get() == null; n++)
                                verify(db, published.get(random.nextInt(published.size())));
                        } catch (Throwable t) { failure.compareAndSet(null, t); }
                    }));
                }
                start.countDown();
                for (Future<?> f : futures) f.get(10, TimeUnit.MINUTES);
                if (failure.get() != null) throw new IllegalStateException("concurrent check failed", failure.get());
                List<Commit> ordered = new ArrayList<>(commits); ordered.sort(Comparator.comparingLong(Commit::time));
                int fromIndex = epoch * WRITERS * count;
                check(ordered.size() == (epoch + 1) * WRITERS * count, "missing completion");
                for (int n = fromIndex; n < ordered.size(); n++) {
                    Commit commit = ordered.get(n); Move m = commit.move;
                    check(n == 0 || ordered.get(n - 1).time < commit.time, "duplicate or unordered transaction time");
                    check(oracle[m.from] == m.beforeFrom && oracle[m.to] == m.beforeTo,
                            "RW read inconsistent with committed order at " + commit.time);
                    // A sample at one unit before the commit must still have the earlier state.
                    if (n % 19 == 0) verify(db, new View(commit.time - 1, oracle.clone(), new TreeMap<>(journal)));
                    oracle[m.from] -= m.amount; oracle[m.to] += m.amount;
                    check(journal.put(journal(commit.time), text(m)) == null, "duplicate journal transaction");
                    if (n % 37 == 0 || n == ordered.size() - 1)
                        views.add(new View(commit.time, oracle.clone(), new TreeMap<>(journal)));
                }
                db.sync(); verify(db, views.get(views.size() - 1));
                System.out.println("epoch=" + epoch + " committed=" + ordered.size() + " snapshots=" + views.size());
            }
        } finally { pool.shutdownNow(); }
        try (Database db = Factory.database().open(path).cacheSizeInMb(64).start()) {
            for (View v : views) verify(db, v);
            check(db.getFirstAvailableLookupTime().units() == 0, "history cut with infinite retention");
        }
        System.out.println("OK D1Ledger commits=" + commits.size() + " snapshots=" + views.size() + " restart=checked");
    }
}
