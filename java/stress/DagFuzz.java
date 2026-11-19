package bergdb.dag;

import java.util.*;

import bergdb.common.StringUtil;

/**
 * Randomized test of the Dag alone, all in memory (no Db, no stream), 2026-10-12.
 * Runs random transactions of puts and deletes and, after each transaction, checks
 * every key at every time against a model. Stops at the first wrong lookup and
 * prints the transactions so far.
 *
 * Usage: java -ea -cp bergdb.jar:. bergdb.dag.DagFuzz firstSeed rounds
 *
 * Properties:
 *   maxnode=N  Max node size (default 8).
 *   keys=N     Number of distinct keys, /k/0 to /k/N-1 (default 50).
 *   n=N        Number of transactions (default 150).
 *   ops=N      Up to N operations per transaction (default 4).
 *   del=0      No deletes.
 *   quiet=1    Do not print the transactions of a failing round.
 *   print=1    Print the Dag after each transaction.
 */
public class DagFuzz {
    static final int MAX_NODE = Integer.getInteger("maxnode", 8);
    static final int KEYS = Integer.getInteger("keys", 50);
    static final int N = Integer.getInteger("n", 150);
    static final int OPS = Integer.getInteger("ops", 4);
    static final boolean DEL = !"0".equals(System.getProperty("del"));
    static final boolean QUIET = "1".equals(System.getProperty("quiet"));
    static final boolean PRINT = "1".equals(System.getProperty("print"));

    static final PointerFollower FOLLOWER = new PointerFollower() {
        public Node followPointer(Node predecessor, int pointerIndex, OpData op) {
            Node result = predecessor.getPointerNode(pointerIndex);
            if (!Pointer.isMem(result)) {
                throw new IllegalStateException("stream pointer");
            }
            op.pointerListener.pointerFollowed(predecessor, pointerIndex, result, Pointer.TYPE_MEMORY);
            return result;
        }
    };

    final long seed;
    final Random rnd;
    final Dag dag;
    final Map<String, TreeMap<Long, String>> model = new TreeMap<String, TreeMap<Long, String>>();
    final List<String> log = new ArrayList<String>();

    DagFuzz(long seed) {
        this.seed = seed;
        this.rnd = new Random(seed);
        this.dag = Dag.createEmpty(0, MAX_NODE, FOLLOWER, Dag.DO_NOTHING_POINTER_CREATED_LISTENER);
    }

    /** Returns null if OK, else a description of the first wrong lookup. */
    String run() {
        PutData pd = dag.newPutData();
        pd.pointerFollower = FOLLOWER;
        GetData gd = dag.newGetData();
        gd.pointerFollower = FOLLOWER;

        for (int i = 1; i <= N; i++) {
            long tt = 10 * i;
            pd.tt = tt;
            int ops = 1 + rnd.nextInt(OPS);
            Set<String> keys = new LinkedHashSet<String>();
            while (keys.size() < ops) {
                keys.add("/k/" + rnd.nextInt(KEYS));
            }
            StringBuilder sb = new StringBuilder("T" + i + " t=" + tt + ":");

            // One transaction, its keys in key order, as Db gives them (Dag.putKvs; record
            // format 8, bergdb 026-25).
            TreeMap<long[], byte[]> batch = new TreeMap<long[], byte[]>(new Comparator<long[]>() {
                public int compare(long[] a, long[] b) { return Keys.compareArrays(a, b); }
            });
            for (String key : keys) {
                String value = DEL && rnd.nextInt(4) == 0 ? null : "v" + tt + key;
                batch.put(Keys.toSegments(key), value == null ? null : StringUtil.toBytes(value));
                model(key).put(tt, value);
                sb.append(value == null ? " del " + key : " put " + key);
            }
            dag.putKvs(batch.keySet().toArray(new long[0][]), batch.values().toArray(new byte[0][]),
                    pd);
            pd.clear();
            log.add(sb.toString());
            if (PRINT) {
                System.out.println(sb);
                dag.printGraph(System.out);
            }

            for (String key : model.keySet()) {
                for (long t = 0; t <= tt; t += 10) {
                    Map.Entry<Long, String> e = model.get(key).floorEntry(t);
                    String expected = e == null ? null : e.getValue();
                    byte[] got = dag.getOne(t, Keys.toSegments(key), gd);
                    String actual = got == null ? null : StringUtil.toString(got);
                    if (expected == null ? actual != null : !expected.equals(actual)) {
                        return "after T" + i + ": key " + key + " at time " + t
                                + ": expected " + expected + ", got " + actual;
                    }
                }
            }
        }
        return null;
    }

    TreeMap<Long, String> model(String key) {
        TreeMap<Long, String> m = model.get(key);
        if (m == null) {
            m = new TreeMap<Long, String>();
            model.put(key, m);
        }
        return m;
    }

    public static void main(String[] args) {
        long first = Long.parseLong(args[0]);
        int rounds = Integer.parseInt(args[1]);
        int fails = 0;

        for (long seed = first; seed < first + rounds; seed++) {
            DagFuzz f = new DagFuzz(seed);
            String error;
            try {
                error = f.run();
            } catch (Throwable e) {
                error = "exception after " + f.log.size() + " transactions: " + e;
            }
            if (error != null) {
                fails++;
                System.out.println("FAIL seed=" + seed + " maxnode=" + MAX_NODE + " keys=" + KEYS
                        + ": " + error);
                if (!QUIET) {
                    for (String s : f.log) {
                        System.out.println("  " + s);
                    }
                }
            }
        }
        System.out.println("Done: " + rounds + " rounds, " + fails + " failures.");
    }
}
