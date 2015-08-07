package bergdb.dag;

import bergdb.dag.Dag.CachePolicy;
import bergdb.dag.Dag.PointerListener;

public interface PointerFollower {
    public Node followPointer(Node predecessor, int pointerIndex, long accessData, 
            PointerListener pointerListener, CachePolicy cachePolicy);
}
