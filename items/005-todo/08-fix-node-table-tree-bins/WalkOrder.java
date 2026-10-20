package bergdb.core;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;

import bergdb.dag.Node;
import bergdb.stream.MemoryStream;

/**
 * 005-08: in the order of Residents.walk (the sweep's seq), how often does a canonical
 * index node come after a canonical index node that a memory pointer of it names (its child)?
 * Breadth-first order would put every child after its parent.
 */
public class WalkOrder {
    public static void main(String[] args) {
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(s).clock(clock).testId().maxNodeSize8().startupDistance(2000).start();
        long time = 1000;
        for (int i = 0; i < 4000; i += 20) {
            time += 10;
            clock.setTime(time);
            Trans.Builder b = db.trans();
            for (int k = i; k < i + 20; k++) b.put("k" + (k * 7919 % 4000), "v" + k);
            db.execute(b.build());
        }
        Db.Internal in = db.internal();
        final List<Node> d = new ArrayList<Node>();
        in.transSeq().visitGotDirtyNodes(Long.MAX_VALUE, new TransSeq.NodeVisitor() {
            public void node(Node node, long tpos, long lastTpos) {
                d.add(node);
            }
        });
        List<Node> walk = Residents.walk(in.superRoot(), in.cache().nodes(), d);
        IdentityHashMap<Node, Integer> place = new IdentityHashMap<Node, Integer>();
        for (int i = 0; i < walk.size(); i++) place.put(walk.get(i), i);
        int pairs = 0, childFirst = 0, canonicalIndex = 0;
        for (Node x : walk) {
            if (!x.isIndexNode() || !x.isCanonical()) continue;
            canonicalIndex++;
            for (int i = 0; i < x.getSize(); i++) {
                Node c = x.getPointerNode(i);
                if (c == null || !c.isIndexNode() || !c.isCanonical()) continue;
                pairs++;
                if (place.get(c) < place.get(x)) childFirst++;
            }
        }
        System.out.println("walk: " + walk.size() + " objects, " + canonicalIndex
                + " canonical index objects; parent-child pairs " + pairs + ", the child first in "
                + childFirst);
        db.stop();
    }
}
