package bergdb.jcstress;

import org.openjdk.jcstress.annotations.Actor;
import org.openjdk.jcstress.annotations.Expect;
import org.openjdk.jcstress.annotations.JCStressTest;
import org.openjdk.jcstress.annotations.Outcome;
import org.openjdk.jcstress.annotations.State;
import org.openjdk.jcstress.infra.results.I_Result;

import bergdb.dag.Handle;
import bergdb.dag.KeyNode;
import bergdb.dag.Klong;
import bergdb.dag.Node;

/**
 * An install against a fast-path read (bergdb item 009; 009-02, 3.4 point 5, 3.5): the
 * pointer holds a live handle with no object (an eviction took it); a loader reads the node
 * again and installs the new object under the handle's monitor, between compareAndSets of
 * the state (NodeCollection.followStreamPointer); a reader reads the pointer with an acquire
 * (getPointee; plainly before bergdb 015-14) and the object with a volatile read, and tests
 * it as the fast path does (Handle.usable). r1: -1 no
 * object yet (the slow path), 1 the object with its contents and usable, 0 the object seen
 * without its contents.
 */
@JCStressTest
@Outcome(id = "-1", expect = Expect.ACCEPTABLE, desc = "No object yet: the slow path.")
@Outcome(id = "1", expect = Expect.ACCEPTABLE, desc = "The object with its contents.")
@Outcome(id = "0", expect = Expect.FORBIDDEN, desc = "The object without its contents.")
@State
public class InstallPublication {
    final KeyNode x = new KeyNode(false);
    final Handle h = new Handle(7);

    public InstallPublication() {
        x.addToEnd(Klong.createKey(new byte[] {1}), h, 200);
    }

    @Actor
    public void loader() {
        KeyNode o = new KeyNode(true);
        o.addToEnd(Klong.createKey(new byte[] {2}), null, 300);
        o.setSpos(200);
        synchronized (h) {
            if (h.casState(Handle.LIVE, Handle.LOADING)) {
                h.obj = o;
                h.casState(Handle.LOADING, Handle.LIVE);
            }
        }
    }

    @Actor
    public void reader(I_Result r) {
        Handle g = (Handle) x.getPointee(0);
        Node o = g.obj;
        if (o == null) {
            r.r1 = -1;
            return;
        }
        boolean full = o.getSpos() == 200 && o.getSize() == 1 && o.getPointerPos(0) == 300;
        r.r1 = full && Handle.usable(o, x.getPointerPos(0)) ? 1 : 0;
    }
}
