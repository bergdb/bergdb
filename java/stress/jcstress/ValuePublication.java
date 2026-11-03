package bergdb.jcstress;

import org.openjdk.jcstress.annotations.Actor;
import org.openjdk.jcstress.annotations.Expect;
import org.openjdk.jcstress.annotations.JCStressTest;
import org.openjdk.jcstress.annotations.Outcome;
import org.openjdk.jcstress.annotations.State;
import org.openjdk.jcstress.infra.results.I_Result;

import bergdb.dag.KeyNode;
import bergdb.dag.Klong;
import bergdb.dag.Pointee;
import bergdb.dag.ValueNode;

/**
 * C5 (bergdb item 009; 009-02, 3.4 point 8): a reader's load puts a value into a pointer
 * (KeyNode.setPointee: a release store, under the node's monitor); another reader reads the
 * pointer with an acquire (getPointee, as the fast path does for every pointer since bergdb
 * 015-14), then the value's position (volatile, set in its constructor) and its bytes (final).
 * r1: -2 the pointer seen empty, 1 the value with its position and bytes, 0 without them.
 */
@JCStressTest
@Outcome(id = "-2", expect = Expect.ACCEPTABLE, desc = "The pointer not seen yet.")
@Outcome(id = "1", expect = Expect.ACCEPTABLE, desc = "The value with its position and bytes.")
@Outcome(id = "0", expect = Expect.FORBIDDEN, desc = "The value without them.")
@State
public class ValuePublication {
    final KeyNode x = new KeyNode(true);

    public ValuePublication() {
        x.addToEnd(Klong.createKey(new byte[] {1}), null, 100);
    }

    @Actor
    public void loader() {
        ValueNode v = new ValueNode(new byte[] {42}, 300);
        x.setPointee(0, v);
    }

    @Actor
    public void reader(I_Result r) {
        Pointee p = x.getPointee(0);
        if (p == null) {
            r.r1 = -2;
            return;
        }
        ValueNode v = (ValueNode) p;
        r.r1 = v.getSpos() == 300 && v.getValue()[0] == 42 ? 1 : 0;
    }
}
