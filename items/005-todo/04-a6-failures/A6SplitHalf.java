package bergdb.dag;

import java.util.*;

/**
 * 005-04: does a space split of a full segment leaf (KeyNode.firstAndSecond) carry the dead
 * klong of A6's kind into the half? T1 nearly fills the root leaf with one-segment keys; T2
 * puts two-segment keys under a new first segment, so the new segment root fills and splits
 * in place while the root leaf is full. Prints, for every key node reachable at T2's time,
 * the compare values that have two key klongs of T2. A tool for bergdb 005-04 only.
 *
 * Usage, with BERGDB a checkout with java/ built:
 *   javac --release 8 -cp BERGDB/java/build/bergdb.jar -d OUT A6SplitHalf.java
 *   java -ea -cp BERGDB/java/build/bergdb.jar:OUT bergdb.dag.A6SplitHalf N
 * N, the keys of T1 (default 5): with 3 the root leaf has room in T2, with 4 to 6 it is full.
 */
public class A6SplitHalf {
    static final PointerFollower FOLLOWER = new PointerFollower() {
        public Node followPointer(Node predecessor, int pointerIndex, OpData op) {
            Node result = predecessor.getPointerNode(pointerIndex);
            op.pointerListener.pointerFollowed(predecessor, pointerIndex, result, Pointer.TYPE_MEMORY);
            return result;
        }
    };

    public static void main(String[] args) {
        int first = Integer.parseInt(args.length > 0 ? args[0] : "5");
        Dag dag = Dag.createEmpty(0, 8, FOLLOWER, Dag.DO_NOTHING_POINTER_CREATED_LISTENER);
        final Set<Node> created = Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());
        PutData pd = dag.newPutData();
        pd.pointerFollower = FOLLOWER;
        pd.nodeChangeListener = new Dag.NodeChangeListener() {
            public void topNodeCreated(TopNode node) {}
            public void keyNodeCreated(KeyNode node) { created.add(node); }
            public void valueNodeCreated(ValueNode node, long[] key) {}
            public void keyNodeChanged(KeyNode node) {}
        };
        KeyNode rootLeaf = dag.getTopDs().getSuperRoot().rootPointer;

        pd.tt = 10;
        for (int i = 0; i < first; i++) {
            dag.putKv(Keys.toSegments("/k/" + i), new byte[] {1}, pd);
            pd.clearFast();
        }
        pd.clear();
        System.out.println("after T1: root leaf size " + rootLeaf.size);

        pd.tt = 20;
        created.clear();
        for (int i = 0; i < 12; i++) {
            dag.putKv(Keys.toSegments("/longer/" + (char) ('a' + i)), new byte[] {2}, pd);
            pd.clearFast();
        }
        pd.clear();

        // Every key node reachable at 20: compare values with two key klongs of time 20.
        Deque<Node> stack = new ArrayDeque<Node>();
        Set<Node> seen = Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());
        stack.push(dag.getTopDs().getSuperRoot().rootPointer);
        while (!stack.isEmpty()) {
            Node x = stack.pop();
            if (!(x instanceof KeyNode) || !seen.add(x)) continue;
            KeyNode k = (KeyNode) x;
            long time = -1;
            Map<Long, List<Integer>> byCv = new LinkedHashMap<Long, List<Integer>>();
            for (int i = 0; i < k.size; i++) {
                long klong = k.klongs[i];
                if (Klong.isTime(klong)) { time = Klong.getTime(klong); continue; }
                if (Klong.getType(klong) != Klong.TYPE_KEY) continue;
                if (k.pointers[i] instanceof KeyNode) stack.push(k.pointers[i]);
                if (time != 20) continue;
                long cv = Klong.getCompareValue(klong);
                if (!byCv.containsKey(cv)) byCv.put(cv, new ArrayList<Integer>());
                byCv.get(cv).add(i);
            }
            for (Map.Entry<Long, List<Integer>> e : byCv.entrySet()) {
                if (e.getValue().size() < 2) continue;
                System.out.println("node " + System.identityHashCode(k)
                        + (k == rootLeaf ? " (the root leaf of T1)" : created.contains(k) ? " (made in T2)" : "")
                        + (k.isSegmentLeaf() ? ", segment leaf" : ", internal")
                        + ": compare value " + Klong.compareValueToString(e.getKey())
                        + " at " + e.getValue() + " of size " + k.size + ", pointing to "
                        + describe(k, e.getValue()));
            }
        }
        System.out.println("root leaf of T1 at 20: size " + rootLeaf.size
                + ", reachable " + seen.contains(rootLeaf));
    }

    static String describe(KeyNode k, List<Integer> idx) {
        StringBuilder sb = new StringBuilder();
        for (int i : idx) {
            Node p = k.pointers[i];
            sb.append(System.identityHashCode(p)).append(p instanceof KeyNode
                    ? (((KeyNode) p).isSegmentLeaf() ? "(segment leaf) " : "(internal) ") : "(value) ");
        }
        return sb.toString().trim();
    }
}
