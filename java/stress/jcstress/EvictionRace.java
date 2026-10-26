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

/**
 * An eviction against a fast-path read (bergdb item 009; 009-02, 3.3 and 3.5): the pointer
 * holds the live handle of a canonical object, written at 200; the evictor kills the handle
 * as Cache3.clockStep and kill do (compareAndSet LIVE to DEAD, the written position, the
 * object no longer canonical, then the object out of the handle); a reader on the fast path
 * reads the pointer, the object and the test (Handle.usable) for a reference of 200. Allowed:
 * no object (the slow path), or the object with its contents, canonical or not, usable
 * either way (it is the version at its position); never the object without its contents.
 * r1: -1 no object, 1 the object usable with its contents, 0 otherwise; r2: 1 if the reader
 * saw the object canonical.
 */
@JCStressTest
@Outcome(id = "-1, 0", expect = Expect.ACCEPTABLE, desc = "No object: the slow path.")
@Outcome(id = "1, 1", expect = Expect.ACCEPTABLE, desc = "The object, still canonical.")
@Outcome(id = "1, 0", expect = Expect.ACCEPTABLE, desc = "The object, no longer canonical: still the version at its position.")
@Outcome(id = "0, .*", expect = Expect.FORBIDDEN, desc = "The object without its contents, or not usable.")
@State
public class EvictionRace {
    final KeyNode x = new KeyNode(false);
    final Handle h = new Handle(7);

    public EvictionRace() {
        KeyNode o = new KeyNode(true);
        o.addToEnd(Klong.createKey(new byte[] {2}), null, 300);
        o.setSpos(200);
        o.setCanonical(true);
        h.obj = o;
        x.addToEnd(Klong.createKey(new byte[] {1}), h, 200);
    }

    @Actor
    public void evictor() {
        if (h.casState(Handle.LIVE, Handle.DEAD)) {
            Node o = h.obj;
            h.writtenPos = o.getSpos();
            o.setCanonical(false);
            h.obj = null;
        }
    }

    @Actor
    public void reader(II_Result r) {
        Handle g = (Handle) x.getPointee(0);
        Node o = g.obj;
        if (o == null) {
            r.r1 = -1;
            r.r2 = 0;
            return;
        }
        boolean canonical = o.isCanonical();
        boolean full = o.getSpos() == 200 && o.getSize() == 1 && o.getPointerPos(0) == 300;
        r.r1 = full && Handle.usable(o, x.getPointerPos(0)) ? 1 : 0;
        r.r2 = canonical ? 1 : 0;
    }
}
