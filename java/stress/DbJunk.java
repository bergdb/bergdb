package bergdb.core;

import java.util.*;

import bergdb.dag.*;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.MemoryStream;

/**
 * Db-level measurement for F1-008-10, 2026-10-15 (Java tier of bergdb 011-11,
 * 8.3): runs a deterministic workload and reports
 * the nodes written, the size of D, and the nodes in D that are not reachable at the
 * time of the last transaction (dead or never reachable).
 *
 * Properties: n (transactions, 2000), keys (5000), ops (max KVs per transaction, 3),
 * exact=1 (exactly ops KVs), maxnode (30), sd (startup distance, 20000), del (percent, 0),
 * seed (1).
 */
public class DbJunk {
    static final int N = Integer.getInteger("n", 2000);
    static final int KEYS = Integer.getInteger("keys", 5000);
    static final int OPS = Integer.getInteger("ops", 3);
    static final boolean EXACT = "1".equals(System.getProperty("exact"));
    static final int MAXNODE = Integer.getInteger("maxnode", 30);
    static final int SD = Integer.getInteger("sd", 20000);
    static final int DEL = Integer.getInteger("del", 0);
    static final long SEED = Long.getLong("seed", 1);

    static Set<Node> idSet() {
        return Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());
    }

    static Set<Node> reachable(Db db, long t) {
        Set<Node> r = idSet();
        GetData gd = db.newGetData();
        TopNode top = db.internal().dag().getTopDs().findSuperRootAtTime(t, gd);
        r.add(top);
        Deque<Node> stack = new ArrayDeque<Node>();
        stack.push(gd.followPointer(top, 0));
        while (!stack.isEmpty()) {
            Node x = stack.pop();
            if (!r.add(x)) continue;
            if (!(x instanceof KeyNode)) continue;
            KeyNode k = (KeyNode) x;
            int sz = k.size;
            long del = k.getDeleteBitmapAtTime(t, sz);
            LinkedHashMap<Long, Integer> last = new LinkedHashMap<Long, Integer>();
            for (int i = 0; i < sz; i++) {
                long klong = k.klongs[i];
                if (Klong.isTime(klong)) {
                    if (Klong.getTime(klong) > t) break;
                    continue;
                }
                if (Klong.getType(klong) != Klong.TYPE_KEY) continue;
                if (Klong.isDeleted(del, i)) continue;
                last.put(Klong.getCompareValue(klong), i);
            }
            for (int i : last.values()) {
                Node c = k.getPointerNode(i);
                if (c == null) c = gd.followPointer(k, i);
                if (c.isIndexNode()) stack.push(c);
            }
        }
        return r;
    }

    public static void main(String[] args) {
        Random rnd = new Random(SEED);
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        DbBuilder b = Db.builder().testSetup(stream).clock(clock).startupDistance(SD);
        if (MAXNODE == 8) b.maxNodeSize8();
        if (MAXNODE == 14) b.maxNodeSize14();
        if (MAXNODE == 30) b.maxNodeSize30();
        if (MAXNODE == 62) b.maxNodeSize62();
        final Db db = b.start();

        long nodes = 0, kvs = 0, sumD = 0, maxD = 0, sumDead = 0, maxDead = 0, samples = 0;
        long time = 10;
        for (int i = 0; i < N; i++) {
            time += 1 + rnd.nextInt(20);
            clock.setTime(time);
            Trans.Builder tb = db.trans();
            int ops = EXACT ? OPS : 1 + rnd.nextInt(OPS);
            for (int o = 0; o < ops; o++) {
                String k = "/k/" + rnd.nextInt(KEYS);
                if (rnd.nextInt(100) < DEL) {
                    tb.delete(k);
                } else {
                    byte[] v = new byte[1 + rnd.nextInt(40)];
                    rnd.nextBytes(v);
                    tb.put(k, v);
                }
            }
            Trans t = tb.build();
            db.execute(t);
            nodes += t.nodeCount;
            kvs += t.kvs.length;

            if (i % 10 == 9 || i == N - 1) {
                final long[] dCount = new long[1];
                final Set<Node> inD = idSet();
                db.internal().transSeq().visitGotDirtyNodes(Long.MAX_VALUE, new TransSeq.NodeVisitor() {
                    public void node(Node node, long tpos, long lastTpos) {
                        dCount[0]++;
                        inD.add(node);
                    }
                });
                Set<Node> now = reachable(db, t.tt);
                long dead = 0;
                for (Node x : inD) if (!now.contains(x)) dead++;
                sumD += dCount[0];
                maxD = Math.max(maxD, dCount[0]);
                sumDead += dead;
                maxDead = Math.max(maxDead, dead);
                samples++;
            }
        }
        db.sync(SyncLevel.ORDINARY);
        System.out.println("n=" + N + " keys=" + KEYS + " ops=" + (EXACT ? "" : "1..") + OPS
                + " maxnode=" + MAXNODE + " sd=" + SD + " del=" + DEL + "% seed=" + SEED);
        System.out.println("  stream bytes " + stream.getLength() + ", nodes written " + nodes
                + " (KVs " + kvs + ")");
        System.out.println("  D: average " + (sumD / samples) + ", max " + maxD
                + "; not reachable at the last time: average " + (sumDead / samples)
                + ", max " + maxDead);
        db.close();
    }
}
