package bergdb.jcstress;

import org.openjdk.jcstress.annotations.Actor;
import org.openjdk.jcstress.annotations.Expect;
import org.openjdk.jcstress.annotations.JCStressTest;
import org.openjdk.jcstress.annotations.Outcome;
import org.openjdk.jcstress.annotations.State;
import org.openjdk.jcstress.infra.results.II_Result;

import bergdb.dag.Handle;
import bergdb.dag.KeyNode;
import bergdb.dag.Klong;
import bergdb.dag.Node;
import bergdb.dag.Pointee;

/**
 * A swizzle against a fast-path read (bergdb 015-14; 016-06/R1, R1-F3, steps 4 and 5): pointer
 * 0 of key node x holds a dead handle a with reference 200; the node's live handle b holds the
 * version at 200, v1. A reader's slow path (the loader here) raises the reference to 300
 * (KeyNode.raiseRef), installs the version at 300, v2, into b under b's monitor, and swizzles b
 * into the pointer (KeyNode.swizzle, a release store); another reader follows the pointer on
 * the fast path (NodeCollection.followPointer): the pointer with an acquire (getPointee), then
 * the reference (getPointerPos) and b's object (volatile). If it sees b, the acquire orders the
 * raise and the install before its next reads. r1: 0 the reader saw a, 1 it saw b; r2: 1 for
 * the raised reference, plus 2 for v2.
 *
 * <p>Forbidden: b with the reference before the raise or with v1. b with 200 and v1 is R1-F3's
 * wrong answer (Handle.usable accepts v1 for 200, a version older than the reader needs). Before
 * 015-14 the reader read the pointer and the reference plainly: AArch64 may then read the
 * reference before the pointer (b with 200 and v2: harmless, but the pair of two moments), and
 * the JMM allows v1 too, which HotSpot does not give, as the read of b's object depends on the
 * address the read of the pointer gave.</p>
 */
@JCStressTest
@Outcome(id = "0, 0", expect = Expect.ACCEPTABLE, desc = "Before the raise: the dead handle (the slow path).")
@Outcome(id = "0, 1", expect = Expect.ACCEPTABLE, desc = "After the raise, before the swizzle: the dead handle.")
@Outcome(id = "1, 3", expect = Expect.ACCEPTABLE, desc = "After the swizzle: b, the raised reference, v2.")
@Outcome(id = "1, 2", expect = Expect.FORBIDDEN, desc = "b with the reference before the raise.")
@Outcome(id = "1, 1", expect = Expect.FORBIDDEN, desc = "b with the object before the install.")
@Outcome(id = "1, 0", expect = Expect.FORBIDDEN, desc = "b, 200 and v1: a version too old (R1-F3).")
@State
public class SwizzleOrder {
    final KeyNode x = new KeyNode(false);
    final Handle a = new Handle(7);
    final Handle b = new Handle(7);
    final KeyNode v1 = version(200);
    final KeyNode v2 = version(300);

    public SwizzleOrder() {
        a.casState(Handle.LIVE, Handle.DEAD);
        b.obj = v1;
        x.addToEnd(Klong.createKey(new byte[] {1}), a, 200);
    }

    static KeyNode version(long spos) {
        KeyNode v = new KeyNode(true);
        v.addToEnd(Klong.createKey(new byte[] {2}), null, 900);
        v.setSpos(spos);
        return v;
    }

    @Actor
    public void loader() {
        x.raiseRef(0, 300);
        synchronized (b) {
            if (b.casState(Handle.LIVE, Handle.LOADING)) {
                b.obj = v2;
                b.casState(Handle.LOADING, Handle.LIVE);
            }
        }
        x.swizzle(0, a, b);
    }

    @Actor
    public void reader(II_Result r) {
        Pointee p = x.getPointee(0);
        long ref = x.getPointerPos(0);
        Node o = ((Handle) p).obj;
        r.r1 = p == b ? 1 : 0;
        r.r2 = (ref == 300 ? 1 : 0) + (o == v2 ? 2 : 0);
    }
}
