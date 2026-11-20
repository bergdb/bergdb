import bergdb.pub.*;
// Single-type import: a3-limits' Limits, in the same unnamed package, hides bergdb.pub.*'s.
import bergdb.pub.Limits;
import bergdb.pub.util.DbException;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.*;

/** Functional API boundary checks. Usage: D5ContractEdges DIR SEED. */
public final class D5ContractEdges {
    public static class Probe {
        public long number; public String text; public byte[] bytes;
        public Probe() { }
        Probe(long n, String t, byte[] b) { number = n; text = t; bytes = b; }
    }
    public static class Chain { public int number; public Chain child; public Chain() { } }
    public static class Invalid { public final int number = 1; public Invalid() { } }
    final Map<String, Object> oracle = new HashMap<>();
    final Random random; long assertions, refusals;
    D5ContractEdges(long seed) { random = new Random(seed); }
    static void check(boolean ok, String message) { if (!ok) throw new IllegalStateException(message); }
    <T extends Throwable> T refused(Class<T> type, Runnable call) {
        try { call.run(); } catch (Throwable t) {
            check(type.isInstance(t), "expected " + type.getSimpleName() + ", got " + t);
            refusals++; return type.cast(t);
        }
        throw new IllegalStateException("expected refusal " + type.getSimpleName());
    }
    static Object copy(Object v) {
        if (v instanceof byte[] b) return b.clone();
        if (v instanceof Probe p) return new Probe(p.number, p.text, p.bytes == null ? null : p.bytes.clone());
        if (v instanceof Chain chain) {
            Chain c = new Chain(); c.number = chain.number;
            c.child = chain.child == null ? null : (Chain) copy(chain.child); return c;
        }
        return v;
    }
    void verify(Connection c) {
        c.setLookupTime(Time.MAX);
        Set<String> keys = new HashSet<>();
        for (Kv<byte[]> e : c.usePrimary(byte[].class).dir("/checks/").kvs()) check(keys.add(e.key()), "duplicate key");
        check(keys.equals(oracle.keySet()), "refusal changed keys: expected=" + oracle.size() + ", got=" + keys.size());
        for (var e : oracle.entrySet()) {
            Object v = e.getValue(); String key = e.getKey(); check(c.exists(key), "missing key " + key);
            if (v instanceof byte[] b) check(Arrays.equals(b, c.get(key, byte[].class)), "changed bytes " + key);
            else if (v instanceof String s) check(s.equals(c.get(key, String.class)), "changed String " + key);
            else if (v instanceof Long n) check(n.equals(c.get(key, Long.class)), "changed Long " + key);
            else if (v instanceof Probe p) {
                Probe got = c.get(key, Probe.class);
                check(got != null && got.number == p.number && Objects.equals(got.text, p.text)
                        && Arrays.equals(got.bytes, p.bytes), "changed object " + key);
            } else if (v instanceof Chain chain) {
                Chain got = c.get(key, Chain.class);
                while (chain != null && got != null) {
                    check(chain.number == got.number, "changed nested field"); chain = chain.child; got = got.child;
                }
                check(chain == null && got == null, "changed nesting depth");
            } else throw new IllegalStateException("unsupported oracle type");
            assertions++;
        }
        assertions++;
    }
    void put(Connection c, String k, Object v) { c.put(k, v); oracle.put(k, copy(v)); }
    static int keyBytes(String k) {
        return k.getBytes(StandardCharsets.UTF_8).length + (int) k.chars().filter(ch -> ch == '/').count();
    }
    void keys(Connection c) {
        for (String piece : new String[]{"a", "\u0000", "\u0001", "ä", "中", "😀"})
            for (int target : new int[]{109, 110, 111, 112, 113}) {
                String prefix = "/checks/"; int available = target - keyBytes(prefix);
                String name = piece.repeat(available / piece.getBytes(StandardCharsets.UTF_8).length);
                String k = prefix + name + "x".repeat(target - keyBytes(prefix + name));
                check(keyBytes(k) == target && Limits.keyBytes(k) == target, "key count mismatch");
                if (target <= 111) { Limits.checkKey(k); put(c, k, "key:" + target); }
                else {
                    refused(IllegalArgumentException.class, () -> Limits.checkKey(k));
                    refused(IllegalArgumentException.class, () -> c.put(k, "refused"));
                    refused(IllegalArgumentException.class, () -> c.delete(k));
                    check(c.get(k, String.class) == null && !c.exists(k), "oversize key reads wrong");
                }
            }
        for (String bad : new String[]{null, "", "/", "plain", "/tail/", "/a//b", "/checks/\ud800", "/checks/\udc00"}) {
            refused(IllegalArgumentException.class, () -> c.put(bad, "bad"));
            refused(IllegalArgumentException.class, () -> c.delete(bad));
            refused(IllegalArgumentException.class, () -> c.get(bad, String.class));
            refused(IllegalArgumentException.class, () -> c.exists(bad));
        }
        verify(c); System.out.println("keys checked");
    }
    void poison(Connection c, String k, Object v, boolean delete) {
        WBuilder w = c.w().put("/checks/poison-before.txt", "must not commit");
        if (delete) refused(IllegalArgumentException.class, () -> w.delete(k));
        else refused(IllegalArgumentException.class, () -> w.put(k, v));
        IllegalStateException execute = refused(IllegalStateException.class, w::execute);
        check(execute.getCause() != null, "spoiled builder lost first cause");
        refused(IllegalStateException.class, () -> w.put("/checks/poison-after.txt", "must not commit"));
        refused(IllegalStateException.class, () -> w.delete("/checks/missing")); verify(c);
    }
    void values(Connection c) {
        byte[] max = new byte[Limits.MAX_VALUE_BYTES]; random.nextBytes(max);
        put(c, "/checks/max.bin", max); verify(c);
        poison(c, "/checks/too-large.bin", new byte[Limits.MAX_VALUE_BYTES + 1], false);
        int n = Limits.MAX_VALUE_BYTES / 3;
        String maxText = "中".repeat(n) + "a".repeat(Limits.MAX_VALUE_BYTES - n * 3);
        put(c, "/checks/max.txt", maxText); verify(c);
        poison(c, "/checks/too-large.txt", maxText + "a", false);
        poison(c, "/checks/bad.txt", "x\ud800y", false);
        poison(c, "/checks/null", null, false);
        poison(c, "/checks/invalid", new Invalid(), false);
        poison(c, "/checks/null-array", new String[]{"a", null}, false);
        poison(c, "/checks/" + "x".repeat(112), "bad", false);
        poison(c, "/checks/" + "x".repeat(112), null, true);
        byte[] bytes = {4, 5, 6}; WBuilder w = c.w().put("/checks/copy.bin", bytes);
        bytes[0] = 99; w.execute(); oracle.put("/checks/copy.bin", new byte[]{4, 5, 6});
        Probe p = new Probe(42, "before", new byte[]{7, 8});
        WBuilder obj = c.w().put("/checks/copy", p); p.number = 1000; p.text = "after"; p.bytes[0] = 99;
        obj.execute(); oracle.put("/checks/copy", new Probe(42, "before", new byte[]{7, 8}));
        Chain good = new Chain(), cursor = good;
        for (int depth = 2; depth <= 16; depth++) {
            cursor.child = new Chain(); cursor = cursor.child; cursor.number = depth;
        }
        put(c, "/checks/depth", good); verify(c);
        cursor.child = new Chain(); poison(c, "/checks/too-deep", good, false); cursor.child = null;
        put(c, "/checks/absent-fields", new Probe(1, null, null)); verify(c);
        refused(ObjectCreationException.class, () -> c.get("/checks/missing", Invalid.class));
        System.out.println("value sizes, copying and object refusals checked");
    }
    void transactions(Connection c) {
        WBuilder good = c.w();
        for (int i = 0; i < 500; i++) good.put("/checks/op" + i + ".txt", "v" + i);
        good.execute();
        for (int i = 0; i < 500; i++) oracle.put("/checks/op" + i + ".txt", "v" + i);
        verify(c);
        WBuilder tooMany = c.w().put("/checks/operation-poison.txt", "no");
        for (int i = 0; i < 500; i++) tooMany.delete("/checks/absent" + i);
        refused(DbException.class, tooMany::execute);
        refused(IllegalStateException.class, tooMany::execute); verify(c);
        WBuilder repeated = c.w();
        for (int i = 0; i < 2000; i++) {
            repeated.put("/checks/repeated.txt", "v" + i); if (i % 2 == 0) repeated.delete("/checks/repeated.txt");
        }
        repeated.execute(); oracle.put("/checks/repeated.txt", "v1999"); verify(c);
        String[] keys = {"/checks/budget-a.bin", "/checks/budget-b.bin", "/checks/budget-c.bin", "/checks/budget-d.bin"};
        int keyCount = Arrays.stream(keys).mapToInt(D5ContractEdges::keyBytes).sum();
        int lastSize = (int) (Limits.MAX_TRANS_BYTES - keyCount - 3L * Limits.MAX_VALUE_BYTES);
        byte[] large = new byte[Limits.MAX_VALUE_BYTES], last = new byte[lastSize];
        Arrays.fill(large, (byte) 73); Arrays.fill(last, (byte) 81);
        WBuilder budget = c.w();
        for (int i = 0; i < 4; i++) budget.put(keys[i], i == 3 ? last : large);
        budget.execute();
        for (int i = 0; i < 4; i++) oracle.put(keys[i], (i == 3 ? last : large).clone());
        verify(c);
        WBuilder overBudget = c.w();
        for (int i = 0; i < 4; i++) overBudget.put(keys[i], i == 3 ? new byte[lastSize + 1] : large);
        refused(DbException.class, overBudget::execute); verify(c);
        System.out.println("operation and transaction byte boundaries checked");
    }
    void environments(Connection c, Database db) throws Exception {
        put(c, "/checks/rw-prior.txt", "old"); AtomicReference<RwEnvironment> escaped = new AtomicReference<>();
        c.rw(env -> {
            escaped.set(env); env.put("/checks/rw-prior.txt", "new");
            refused(IllegalArgumentException.class, () -> env.put("/checks/bad.txt", "\ud800"));
            refused(IllegalArgumentException.class, () -> env.delete("/checks/" + "x".repeat(112)));
            check(env.get("/checks/rw-prior.txt", String.class).equals("old"), "RW saw own value");
            env.put("/checks/rw-other.txt", "accepted"); env.setOutput("o", "done");
        });
        oracle.put("/checks/rw-prior.txt", "new"); oracle.put("/checks/rw-other.txt", "accepted"); verify(c);
        RwEnvironment env = escaped.get();
        refused(IllegalStateException.class, () -> env.put("/checks/escaped.txt", "bad"));
        refused(IllegalStateException.class, () -> env.get("/checks/rw-prior.txt", String.class));
        refused(IllegalStateException.class, () -> env.setOutput("late", "bad"));
        RuntimeException deliberate = new RuntimeException("action refusal");
        RuntimeException got = refused(RuntimeException.class, () -> c.rw(e -> { e.put("/checks/thrown.txt", "bad"); throw deliberate; }));
        check(got == deliberate, "action exception changed"); verify(c);
        ExecutorService threads = Executors.newFixedThreadPool(3);
        try {
            c.rw(e -> {
                List<Future<?>> fs = new ArrayList<>();
                for (int n = 0; n < 3; n++) {
                    int worker = n; fs.add(threads.submit(() -> {
                        for (int j = 0; j < 12; j++) {
                            check(e.get("/checks/rw-prior.txt", String.class).equals("new"), "parallel env read differs");
                            e.put("/checks/parallel" + worker + "-" + j + ".txt", worker + ":" + j);
                        }
                    }));
                }
                for (Future<?> f : fs) try { f.get(10, TimeUnit.SECONDS); }
                catch (Exception x) { throw new IllegalStateException(x); }
            });
            for (int w = 0; w < 3; w++) for (int j = 0; j < 12; j++)
                oracle.put("/checks/parallel" + w + "-" + j + ".txt", w + ":" + j);
            WBuilder waiting = c.w().put("/checks/waiting.txt", "eventually");
            CountDownLatch entered = new CountDownLatch(1), release = new CountDownLatch(1);
            Future<?> transaction = threads.submit(() -> c.rw(e -> {
                entered.countDown();
                try { check(release.await(10, TimeUnit.SECONDS), "release timeout"); }
                catch (InterruptedException x) { throw new IllegalStateException(x); }
                e.put("/checks/holding.txt", "committed");
            }));
            check(entered.await(10, TimeUnit.SECONDS), "action did not start");
            try {
                refused(IllegalStateException.class, () -> c.get("/checks/rw-prior.txt", String.class));
                refused(IllegalStateException.class, waiting::execute);
                refused(IllegalStateException.class, () -> c.setLookupTime(Time.MAX));
                refused(IllegalStateException.class, db::connection);
            } finally { release.countDown(); }
            transaction.get(10, TimeUnit.SECONDS); oracle.put("/checks/holding.txt", "committed");
            waiting.execute(); oracle.put("/checks/waiting.txt", "eventually"); verify(c);
        } finally { threads.shutdownNow(); }
        c.setEnableKeyReplace(true);
        WBuilder captured = c.w().put("/checks/${transactionTime}.txt", "captured true");
        c.setEnableKeyReplace(false); long time = captured.execute().getTime().units();
        oracle.put("/checks/" + String.format(Locale.ROOT, "%018d", time) + ".txt", "captured true");
        WBuilder literal = c.w().put("/checks/${transactionTime}.txt", "captured false");
        c.setEnableKeyReplace(true); literal.execute(); oracle.put("/checks/${transactionTime}.txt", "captured false");
        Transaction rw = c.rw(e -> { c.setEnableKeyReplace(false); e.put("/checks/rw-${transactionTime}.txt", "captured rw"); });
        oracle.put("/checks/rw-" + String.format(Locale.ROOT, "%018d", rw.getTime().units()) + ".txt", "captured rw");
        verify(c);
        System.out.println("RW refusals, lifetimes, parallel environments and connection ownership checked");
    }
    void indexes(Connection c, Database db) {
        db.indexBuilder("by-number").dir("/checks/").type("long").field("number").start().join();
        WBuilder initial = c.w();
        for (int n = 0; n < 167; n++) initial.put("/checks/index" + n, new Probe(n, null, null));
        initial.execute();
        for (int n = 0; n < 167; n++) oracle.put("/checks/index" + n, new Probe(n, null, null));
        WBuilder accepted = c.w();
        for (int n = 0; n < 166; n++) accepted.put("/checks/index" + n, new Probe(n + 10000, null, null));
        accepted.execute();
        for (int n = 0; n < 166; n++) oracle.put("/checks/index" + n, new Probe(n + 10000, null, null));
        verify(c);
        WBuilder over = c.w();
        for (int n = 0; n < 167; n++) over.put("/checks/index" + n, new Probe(n + 20000, null, null));
        refused(DbException.class, over::execute); verify(c);
        db.indexBuilder("text-limit").dir("/checks/").type("string").field("text").start().join();
        db.indexBuilder("bytes-limit").dir("/checks/").type("bytes").field("bytes").start().join();
        for (String text : new String[]{"a".repeat(110), "\u0000".repeat(55), "\u0001".repeat(55), "中".repeat(36) + "ab"}) {
            put(c, "/checks/level", new Probe(12345, text, new byte[]{1})); verify(c);
        }
        for (String text : new String[]{"a".repeat(111), "\u0000".repeat(56), "\u0001".repeat(56), "中".repeat(37)}) {
            WBuilder w = c.w().put("/checks/index-poison.txt", "bad").put("/checks/level", new Probe(99999, text, null));
            refused(IllegalArgumentException.class, w::execute); verify(c);
        }
        put(c, "/checks/byte-level", new Probe(30000, null, new byte[55])); verify(c);
        refused(IllegalArgumentException.class, () -> c.put("/checks/byte-level", new Probe(40000, null, new byte[56])));
        verify(c);
        List<String> wanted = new ArrayList<>();
        for (var e : oracle.entrySet())
            if (e.getValue() instanceof Probe || e.getValue() instanceof Chain) wanted.add(e.getKey());
        wanted.sort(Comparator.comparingLong((String k) -> oracle.get(k) instanceof Probe p ? p.number : ((Chain) oracle.get(k)).number).thenComparing(k -> k));
        List<String> got = new ArrayList<>();
        for (Kv<Probe> e : c.useIndex("by-number", Probe.class).kvs()) {
            got.add(e.key()); Object expected = oracle.get(e.key());
            long number = expected instanceof Probe p ? p.number : ((Chain) expected).number;
            check(e.value().number == number, "index value damaged");
        }
        check(got.equals(wanted), "index contents changed by refusal");
        System.out.println("indexed operation and level boundaries checked");
    }
    public static void main(String[] args) throws Exception {
        String path = args[0]; long seed = Long.parseLong(args[1]);
        check(!Files.exists(Path.of(path)), "use a fresh directory");
        System.out.println("Kind: functional; D5ContractEdges seed=" + seed);
        D5ContractEdges app = new D5ContractEdges(seed);
        try (Database db = Factory.database().create(path).cacheSizeInMb(96).start()) {
            Connection c = db.connection();
            app.keys(c); app.values(c); app.transactions(c); app.environments(c, db); app.indexes(c, db);
            db.sync(); app.verify(c);
        }
        try (Database db = Factory.database().open(path).cacheSizeInMb(96).start()) { app.verify(db.connection()); }
        System.out.println("OK D5ContractEdges assertions=" + app.assertions + " refused=" + app.refusals + " restart=checked");
    }
}
