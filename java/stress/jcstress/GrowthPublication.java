package bergdb.jcstress;

import org.openjdk.jcstress.annotations.Actor;
import org.openjdk.jcstress.annotations.Expect;
import org.openjdk.jcstress.annotations.JCStressTest;
import org.openjdk.jcstress.annotations.Outcome;
import org.openjdk.jcstress.annotations.State;
import org.openjdk.jcstress.infra.results.III_Result;

import bergdb.dag.Handle;
import bergdb.dag.KeyNode;
import bergdb.dag.Klong;
import bergdb.dag.Pointee;

/**
 * A key node's growth against a reader (bergdb 015-12; 016-06/R1, R1-F1): the node is full,
 * 14 klongs in arrays of 14, each with a pointer to a handle and a reference; the writer
 * appends one more (KeyNode.addToEnd), which replaces the three arrays by copies of 30
 * (growCapacity) before it raises the size; a reader reads the size, then the three array
 * fields, volatile since bergdb 015-14 (plain, after a release fence of the writer's, in
 * 015-12), as the searches and the fast path do, and every element below the size it read.
 * Allowed: the old arrays, or the new ones with the copies; never a new array without them (a
 * klong 0, a null pointer, a reference 0 below the size). r1: the size read, 14 or 15; r2: 1
 * if the reader saw a new array, 0 if only old ones; r3: 1 if every element below the size is
 * the one the writer put there, 0 if not.
 */
@JCStressTest
@Outcome(id = "14, 0, 1", expect = Expect.ACCEPTABLE, desc = "Before the growth: the old arrays.")
@Outcome(id = "14, 1, 1", expect = Expect.ACCEPTABLE_INTERESTING, desc = "The old size, a new array with the copies.")
@Outcome(id = "15, 1, 1", expect = Expect.ACCEPTABLE, desc = "After the append: the new arrays.")
@Outcome(id = ".*, .*, 0", expect = Expect.FORBIDDEN, desc = "An element below the size without its copy.")
@Outcome(id = "15, 0, .*", expect = Expect.FORBIDDEN, desc = "The new size with an old array.")
@State
public class GrowthPublication {
    static final int N = 14;
    static final long[] KEYS = new long[N + 1];

    static {
        for (int i = 0; i <= N; i++) KEYS[i] = Klong.createKey(new byte[] {(byte) (i + 1)});
    }

    final KeyNode x = new KeyNode(false);
    final Handle h = new Handle(7);
    final long[] old;

    public GrowthPublication() {
        for (int i = 0; i < N; i++) x.addToEnd(KEYS[i], h, 1000 + 8 * i);
        old = x.klongs;
    }

    @Actor
    public void writer() {
        x.addToEnd(KEYS[N], h, 1000 + 8 * N);
    }

    @Actor
    public void reader(III_Result r) {
        int s = x.size;                 // volatile, as the searches
        long[] kl = x.klongs;           // volatile, as the searches
        Pointee[] p = x.pointers;       // volatile, as getPointee
        long[] ps = x.pos;              // volatile, as getPointerPos
        boolean full = true;
        for (int i = 0; i < s; i++) {
            if (kl[i] != KEYS[i] || p[i] != h || ps[i] != 1000 + 8 * i) full = false;
        }
        r.r1 = s;
        r.r2 = kl != old || p.length != N || ps.length != N ? 1 : 0;
        r.r3 = full ? 1 : 0;
    }
}
