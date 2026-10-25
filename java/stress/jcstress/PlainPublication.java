package bergdb.jcstress;

import org.openjdk.jcstress.annotations.Actor;
import org.openjdk.jcstress.annotations.Expect;
import org.openjdk.jcstress.annotations.JCStressTest;
import org.openjdk.jcstress.annotations.Outcome;
import org.openjdk.jcstress.annotations.State;
import org.openjdk.jcstress.infra.results.I_Result;

/**
 * The control (bergdb item 009; 009-02, 3.1): an object with a plain field, published by a
 * plain store and read plainly, with no edge between them. The Java Memory Model allows a
 * reader to see the object without its field; on a weakly ordered machine (AArch64) it may
 * show, which tells that the harness can see such races.
 */
@JCStressTest
@Outcome(id = "-2", expect = Expect.ACCEPTABLE, desc = "Not seen yet.")
@Outcome(id = "1", expect = Expect.ACCEPTABLE, desc = "Seen with its field.")
@Outcome(id = "0", expect = Expect.ACCEPTABLE_INTERESTING, desc = "Seen without its field: a race.")
@State
public class PlainPublication {
    static final class Box {
        int f;

        Box() {
            f = 1;
        }
    }

    Box box;

    @Actor
    public void writer() {
        box = new Box();
    }

    @Actor
    public void reader(I_Result r) {
        Box b = box;
        r.r1 = b == null ? -2 : b.f;
    }
}
