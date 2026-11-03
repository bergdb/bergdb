package bergdb.jcstress;

import org.openjdk.jcstress.annotations.Actor;
import org.openjdk.jcstress.annotations.Expect;
import org.openjdk.jcstress.annotations.JCStressTest;
import org.openjdk.jcstress.annotations.Outcome;
import org.openjdk.jcstress.annotations.State;
import org.openjdk.jcstress.infra.results.II_Result;

import bergdb.dag.Handle;
import bergdb.dag.KeyNode;
import bergdb.dag.Node;
import bergdb.dag.Pointee;
import bergdb.dag.Spos;
import bergdb.dag.TopNode;

/**
 * SwizzleOrder for a top node's root pointer (bergdb 015-14; 016-06/R1, R1-F3), which every
 * get follows (TopDs.findRoot): TopNode's pointers changed in place by plain stores under the
 * node's monitor before 015-14, read plainly; now by release and opaque stores, read with an
 * acquire and then an opaque read. The outcomes as SwizzleOrder's.
 */
@JCStressTest
@Outcome(id = "0, 0", expect = Expect.ACCEPTABLE, desc = "Before the raise: the dead handle (the slow path).")
@Outcome(id = "0, 1", expect = Expect.ACCEPTABLE, desc = "After the raise, before the swizzle: the dead handle.")
@Outcome(id = "1, 3", expect = Expect.ACCEPTABLE, desc = "After the swizzle: b, the raised reference, v2.")
@Outcome(id = "1, 2", expect = Expect.FORBIDDEN, desc = "b with the reference before the raise.")
@Outcome(id = "1, 1", expect = Expect.FORBIDDEN, desc = "b with the object before the install.")
@Outcome(id = "1, 0", expect = Expect.FORBIDDEN, desc = "b, 200 and v1: a version too old (R1-F3).")
@State
public class TopSwizzleOrder {
    final TopNode x = new TopNode(0, null, 200, 1, Spos.NULL);
    final Handle a = new Handle(7);
    final Handle b = new Handle(7);
    final KeyNode v1 = SwizzleOrder.version(200);
    final KeyNode v2 = SwizzleOrder.version(300);

    public TopSwizzleOrder() {
        a.casState(Handle.LIVE, Handle.DEAD);
        b.obj = v1;
        x.setPointee(0, a);
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
