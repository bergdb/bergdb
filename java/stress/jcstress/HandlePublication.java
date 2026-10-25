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
 * T6b (bergdb item 009; items/009-handles/02-implementation-plan.md, 3.4): a resolver puts a
 * new handle into a pointer that held nothing (KeyNode.setPointee, under the node's monitor),
 * the handle's object installed before it with a volatile write (Handle.obj); a reader on the
 * fast path reads the pointer plainly (getPointee, as NodeCollection.followPointer does for a
 * pointer to an index node) and then the object with a volatile read. r1: -2 the pointer seen
 * empty, -1 the handle seen without its object (the slow path), 1 the object with its
 * contents (its position, set before the install), 0 the object without them; r2: the
 * handle's id (final, 3.4 point 4), 0 if seen without it.
 */
@JCStressTest
@Outcome(id = "-2, 0", expect = Expect.ACCEPTABLE, desc = "The pointer not seen yet.")
@Outcome(id = "1, 7", expect = Expect.ACCEPTABLE, desc = "The handle, its id, its object with its contents.")
@Outcome(id = "-1, 7", expect = Expect.ACCEPTABLE_INTERESTING, desc = "The handle without its object: the slow path.")
@Outcome(id = "0, 7", expect = Expect.FORBIDDEN, desc = "The object without its contents.")
@Outcome(id = ".*, 0", expect = Expect.FORBIDDEN, desc = "The handle without its id.")
@State
public class HandlePublication {
    final KeyNode x = new KeyNode(false);

    public HandlePublication() {
        x.addToEnd(Klong.createKey(new byte[] {1}), null, 100);
    }

    @Actor
    public void resolver() {
        KeyNode child = new KeyNode(true);
        child.setSpos(200);
        Handle h = new Handle(7);
        h.obj = child;                  // the install: a volatile write
        x.setPointee(0, h);             // the swizzle, under x's monitor
    }

    @Actor
    public void reader(II_Result r) {
        Pointee p = x.getPointee(0);    // plain (T6b)
        if (p == null) {
            r.r1 = -2;
            r.r2 = 0;
            return;
        }
        Handle h = (Handle) p;
        r.r2 = (int) h.id;
        Node o = h.obj;                 // volatile
        r.r1 = o == null ? -1 : o.getSpos() == 200 ? 1 : 0;
    }
}
