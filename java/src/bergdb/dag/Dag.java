package bergdb.dag;

import java.io.PrintStream;
import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Set;
import bergdb.common.Bug;
import bergdb.dag.GetMany.StopCondition;
import bergdb.pub.util.DbException;

/**
 * <p>The Dag (directed acyclic graph) is the main data structure of the database.</p>
 * 
 * <p>Features/scope:</p>
 * <ul>
 * <li>Walking the Dag.</li>
 * <li>getOne(), getMany(), putOne()</li>
 * <li>Dag testable in isolation (Db instance not needed)</li>
 * <li>Reads nodes (from interface NodeReader instance)</li>
 * <li>Factory methods: newGetData(), newGetMany(), new PutData().</li>
 * </ul>
 * 
 * <p>Not in scope:</p>
 * <ul>
 * <li>DbClock - clock for the database</li>
 * <li>Concurrency - the nodes' monitors and the handles' (bergdb item 009).</li>
 * <li>Transaction: collecting transaction node set, adding transaction nodes
 * to stream, ...</li>
 * <li>STM implementation</li>
 * <li>TransSeq</li>
 * <li>followPointer() implementation</li>
 * <li>node caching</li>
 * </ul>
 * 
 * <p>This class was created in September 2013 during a heavy refactoring.
 * I wanted a smaller, cleaner Db class and a Dag class that is testable in isolation.
 * This is a change to review the code for correctness and add more unit test
 * to show that code works. The refactoring was done without much performance penalty.</p> 
 * 
 * @author Frans Lundberg
 */
public class Dag {
    /** Empty array of KlongWithPointer (new KlongWithPointer[0]). */
    private static final KlongWithPointer[] ZERO_LONG_KWP = new KlongWithPointer[0];    
    private final TopDs topDs;
    private final int maxNodeSize;
    
    public Dag(TopNode superRoot, int maxNodeSize) {
        this.topDs = new TopDs(superRoot);
        this.maxNodeSize = maxNodeSize;
    }
    
    /**
     * Factory method to create minimal Dag with two nodes: a top node and a key node.
     * The database is empty; no KVs.
     */
    public static Dag createEmpty(long time, int maxNodeSize, PointerFollower pointerFollower, 
            Dag.PointerCreatedListener pointerCreationListener) {
        return new Dag(time, maxNodeSize, pointerFollower, pointerCreationListener);
    }
    
    private Dag(long time, int maxNodeSize, PointerFollower pointerFollower, Dag.PointerCreatedListener pointerCreationListener) {
        this.topDs = TopDs.createFromFirstRoot(time, new KeyNode(), AccessData.DEFAULT_ACCESS_DATA,
                pointerCreationListener);
        this.maxNodeSize = maxNodeSize;
    }
        
    // ======== General utility methods ========
    
    /**
     * Prints the in memory part of the DB graph. Useful for test and development.
     */
    public void printGraph(PrintStream out) {
        TopNode top = topDs.getSuperRoot();
        top.printGraph(out, "", 0);
    }
    
    public void visitMemoryPointersOnce(PointerVisitor visitor) {
        HashSet<Node> visited = new HashSet<Node>();
        
        Pointer pointer = new Pointer();   // mutable memory to avoid mem alloc.
        Node superRoot = topDs.getSuperRoot();
        visitMemoryPointersOnceFromNode(superRoot, visitor, pointer, visited);
    }
    
    /**
     * Visits 'start' and the nodes below it in memory, each once, depth first: a node, then
     * for each of its pointers in memory, in order, the pointer and the walk from its node.
     * A loop with a stack of its own, the WalkPath, not a recursion (bergdb 021-16): a key
     * has a level of key nodes per segment of 7 bytes, so a long key made the recursion
     * overflow the thread's stack.
     */
    private void visitMemoryPointersOnceFromNode(Node start, PointerVisitor visitor, 
            Pointer pointer, HashSet<Node> visited) {
        if (visited.contains(start)) {
            return;
        }
        
        visited.add(start);
        visitor.visitNode(start);
        
        final WalkPath path = new WalkPath(start);
        while (!path.isEmpty()) {
            final Node node = path.node();
            final int i = path.nextIndex();
            if (i < 0) {
                path.pop();
                continue;
            }
            
            node.getPointer(i, pointer);
            if (pointer.isMem()) {
                visitor.visitPointer(node, pointer);
                
                Node child = pointer.getNode();
                if (!visited.contains(child)) {
                    visited.add(child);
                    visitor.visitNode(child);
                    path.push(child);
                }
            }
        }
    }

    /**
     * Visits all nodes cached in memory.
     */
    public void visitMemoryNodes(NodeVisitor visitor) {
        Set<Node> visited = new HashSet<Node>();
        Node start = topDs.getSuperRoot();
        visitNodeWithChildren(visitor, visited, start);
    }
    
    /**
     * Visits 'start' and the nodes below it in memory, each once, depth first: a node, then
     * the walks from the nodes of its pointers in memory, in order. A loop with a stack of
     * its own, as visitMemoryPointersOnceFromNode(), not a recursion (bergdb 021-16): with
     * the JVM's default stack, a database with a key of about 90 KB or more did not start,
     * as the start's check (DbStarter.postStartupCheck) walks the nodes with this method.
     */
    private void visitNodeWithChildren(NodeVisitor visitor, Set<Node> visited, Node start) {
        if (visited.contains(start)) {
            return;
        } else {
            visited.add(start);
        }
        
        start.accept(visitor);
        
        final Pointer p = new Pointer();
        final WalkPath path = new WalkPath(start);
        while (!path.isEmpty()) {
            final Node node = path.node();
            final int i = path.nextIndex();
            if (i < 0) {
                path.pop();
                continue;
            }
            
            node.getPointer(i, p);
            if (p.isMem()) {
                final Node child = p.getNode();
                if (!visited.contains(child)) {
                    visited.add(child);
                    child.accept(visitor);
                    path.push(child);
                }
            }
        }
    }
    
    /**
     * The stack of a depth-first walk of nodes (bergdb 021-16): the nodes from the walk's
     * start to the node it is at, each with its size, read when the walk came to the node
     * (after its visit, as the recursion before read it), and the index of its next pointer
     * to look at. It replaces the frames of a recursion, so the walk's depth is bounded by
     * the heap, not by the thread's stack.
     */
    private static final class WalkPath {
        private Node[] nodes = new Node[16];
        private int[] sizes = new int[16];
        private int[] next = new int[16];
        private int depth = 0;
        
        WalkPath(Node start) {
            push(start);
        }
        
        boolean isEmpty() {
            return depth == 0;
        }
        
        void push(Node node) {
            if (depth == nodes.length) {
                nodes = java.util.Arrays.copyOf(nodes, 2 * depth);
                sizes = java.util.Arrays.copyOf(sizes, 2 * depth);
                next = java.util.Arrays.copyOf(next, 2 * depth);
            }
            nodes[depth] = node;
            sizes[depth] = node.getSize();
            next[depth] = 0;
            depth++;
        }
        
        void pop() {
            depth--;
            nodes[depth] = null;
        }
        
        /** The node the walk is at. */
        Node node() {
            return nodes[depth - 1];
        }
        
        /** The index of the next pointer of node() to look at, or -1 after its last. */
        int nextIndex() {
            final int top = depth - 1;
            final int i = next[top];
            if (i >= sizes[top]) {
                return -1;
            }
            next[top] = i + 1;
            return i;
        }
    }
    
    public TopDs getTopDs() {
        return topDs;
    }

    public Node findNode(int[] choices, GetData gd) {        
        if (choices == null) {
            throw new IllegalArgumentException("choices == null not allowed");
        }
        
        Node node = topDs.getSuperRoot();
        
        for (int i = 0; i < choices.length; i++) {
            int choice = choices[i];
            
            node = gd.followPointer(node, choice);
            
            if (node == null) {
                break;
            }
        }
        
        return node;
    }
    
    /**
     * Creates a GetData object suitable for use with as a parameter to Dag.getOne().
     * Use Db.newGetData() instead if you want to use the GetData object
     * in Db.getOne(). The caller sets its pointerFollower, as Db.newGetData() does: a Dag
     * has none of its own since 2017 (OpData.followPointer asserts that it is set).
     */
    public GetData newGetData() {
        final GetData g = new GetData();
        
        g.pointerListener = new Dag.PointerListener() {
            public void pointerFollowed(
                    Node predecessor, int pointerIndex, Node result, int pointerType) {
                switch (pointerType) {
                case Pointer.TYPE_MEMORY:
                    g.followMemoryPointerCount++;
                    break;
                case Pointer.TYPE_STREAM:
                    g.followStreamPointerCount++;
                    break;
                default:
                    assert false : "Bad pointer type: " + pointerType + ".";
                    break;
                }
            }

            public void superRootAccessed(TopNode superRoot) {}
        };
        
        return g;
    }
    
    /**
     * This is the preferred way to create a GetMany object used together with 
     * this Dag object.
     */
    public GetMany newGetMany() {
        return new GetMany();
    }
    
    /**
     * Creates a PutData object suitable for use with as a parameter to Dag.putKv().
     * Use Db.newPutData() instead if you want to use the PutData object as a 
     * parameter with methods of Db. The caller sets its pointerFollower, as Db does.
     */
    public PutData newPutData() {        
        final PutData p = new PutData();
        
        p.pointerListener = new Dag.PointerListener() {
            public void pointerFollowed(
                    Node predecessor, int pointerIndex, Node result, int pointerType) { 
                if (result != null) {
                    if (result.getType() == Node.TYPE_KEY_NODE) {
                        if (predecessor.getType() == Node.TYPE_TOP_NODE) {
                            p.keyAccessPath.add(Klong.NULL, (KeyNode) result); 
                        } else if (predecessor.getType() == Node.TYPE_KEY_NODE) {
                            KeyNode pre = (KeyNode) predecessor;
                            KeyNode res = (KeyNode) result;
                            p.keyAccessPath.add(pre.getKlong(pointerIndex), res);
                        }
                    }
                }
            }

            public void superRootAccessed(TopNode superRoot) {}
        };
        
        p.splitListener = new SplitListener() {
            public void nodeSplit(int splitType) {
                switch (splitType) {
                case TIME_SPLIT_1:
                case TIME_SPLIT_2:
                    p.timeSplitCount += 1;
                    break;
                case SPACE_SPLIT_1:
                case SPACE_SPLIT_2:
                case SPACE_SPLIT_3:
                    p.spaceSplitCount += 1;
                    break;
                }
            }
        };
        
        return p;
    }
    
    // ==== getOne() with helpers ========
    
    /**
     * Gets one KV value or returns null if it does not exist.
     * gd.kvTime is set if a value is found.
     * gd.tpos is set if a value is found: ValueNode.getTpos(), Spos.NULL if it is not
     * written yet.
     * 
     * @param time  The lookup time.
     * @throws StreamFormatException
     * @throws StreamIoException
     */
    public byte[] getOne(long time, long[] keySegments, final GetData gd) {
        assert gd.pointerListener != null;
        assert gd.cachePolicy != null;
        
        KeyNode segmentRoot = topDs.findRoot(time, gd);

        if (segmentRoot == null) {
            return null;
        }
        
        Node item;
        KeyNode node;
        final int segmentCount = keySegments.length;
        final int lastIndex = keySegments.length - 1;
        byte[] result = null;

        for (int i = 0; i < segmentCount; i++) {
            item = getEqNodeInSegment(time, segmentRoot, keySegments[i], gd);

            if (i == lastIndex) {
                result = null;
                if (item != null && item instanceof ValueNode) {
                    ValueNode valueNode = (ValueNode) item;
                    result = valueNode.getValue();
                    gd.tpos = valueNode.getTpos();
                }
                break;
            } else {
                if (item instanceof KeyNode) {
                    node = (KeyNode) item;
                } else {
                    node = null;
                }

                if (node == null) {
                    result = null;
                    break;
                }
                gd.nodeDepth++;
                segmentRoot = node;
            }
        }
        
        return result;
    }
    
    /**
     * Gets a ValueNode or KeyNode from a segment in the Db graph. Returns null
     * if none was found.
     * 
     * @param time
     *            The lookup time.
     * @param segmentRoot
     *            The segment root key node.
     * @param compareValue
     *            The compareValue to search for.
     * @param gd
     *            GetData to the lookup operation.
     * @throws StreamFormatException
     * @throws StreamIoException
     */
    private final Node getEqNodeInSegment(long time, KeyNode segmentRoot, long compareValue,
            GetData gd) {
        final KlongWithPointer kwi = gd.kwi;
        KeyNode current = segmentRoot;
        Node result;
        gd.descentFrom(current);

        while (true) {
            if (current.isSegmentLeaf()) {
                current.searchEq(time, compareValue, kwi);

                if (kwi.klong == Klong.NULL) {
                    result = null;
                } else {
                    assert !kwi.isNullPointer()
                            : "bad pointer " + kwi.pointerIndex + " of node " + current
                              + ", KeyNode.searchEq() found result, but there is no pointer "
                              + "(no mem pointer, no stream pointer)";
                    
                    result = gd.followPointer(current, kwi.pointerIndex);
                    gd.kvTime = kwi.klongTime;
                }
                break;

            } else {
                current.searchLte(time, compareValue, kwi);

                if (kwi.klong == Klong.NULL) {
                    result = null;
                    break;
                } else {
                    assert kwi.node == null || kwi.node instanceof KeyNode 
                            : "Expected a KeyNode, got " + kwi.node;

                    KeyNode nextCurrent = (KeyNode) gd.followPointer(current, kwi.pointerIndex);
                    gd.descentTo(nextCurrent);
                    current = nextCurrent;
                }
            }
        }

        return result;
    }
    
    /**
     * Follows the index nodes on the path of a key at 'time': the super root, the space root
     * and, in each segment's tree, the nodes down to the segment leaf of the key's segment,
     * as putKv() and getOne() follow them (searchLte in an inner node, searchEq in a segment
     * leaf), but not the pointer to the key's value. It stops where the path ends: a segment
     * that no key has. For the touch of a reclaim step (Db.touchPaths; bergdb 024-07), whose
     * pointer listener in 'gd' makes the nodes dirty.
     * 
     * @param time  The lookup time.
     * @throws StreamFormatException
     * @throws StreamIoException
     */
    public void followPath(long time, long[] keySegments, final GetData gd) {
        final KlongWithPointer kwi = gd.kwi;
        final int lastIndex = keySegments.length - 1;
        KeyNode current = topDs.findRoot(time, gd);
        
        for (int i = 0; current != null; i++) {
            gd.descentFrom(current);
            while (!current.isSegmentLeaf()) {
                current.searchLte(time, keySegments[i], kwi);
                if (kwi.klong == Klong.NULL) {
                    return;
                }
                final KeyNode next = (KeyNode) gd.followPointer(current, kwi.pointerIndex);
                gd.descentTo(next);
                current = next;
            }
            if (i == lastIndex) {
                return;     // The segment leaf that holds the key's klong, or would.
            }
            current.searchEq(time, keySegments[i], kwi);
            if (kwi.klong == Klong.NULL) {
                return;
            }
            final Node item = gd.followPointer(current, kwi.pointerIndex);
            current = item instanceof KeyNode ? (KeyNode) item : null;
        }
    }
    
    
    // ======== dirtyNodeBound() ========
    
    /**
     * An upper bound on the number of index nodes that a transaction with these puts and
     * deletes, at a later time, can make dirty or create (2026-10-24, bergdb 005-31), for
     * Db's check before the go point. Walks the paths of the keys at 'time', as a get does,
     * loading nodes. Counts:
     * 
     * <ul>
     * <li>the distinct key nodes on the paths: a put makes dirty its leaf and every node above
     * it, up to the space root;</li>
     * <li>the nodes that splits can make. A node that gets k klongs (one for each put and each
     * new segment below it, those of its children's splits, and a TIME klong) with room for r
     * more overflows at most once if k exceeds r, and once more for every further half node
     * of klongs (a replacement holds at most h klongs, a half node, or c + 1, a merged
     * node): 1 + (k - r - 1) / q times, q = roomAfterReplacement(), 10 at node size 30
     * (M/2 - 3 or 1 until format 7). The first overflow of a node that existed replaces it
     * by up to two new nodes and adds two klongs to its parent; later ones split new nodes in
     * place, one new node and one klong each. An overflow of the space root adds a new root;</li>
     * <li>the new segment trees of keys whose segment is not there, counted the same way from
     * an empty node;</li>
     * <li>for a delete (bergdb 023-07, section 5.4, K4): two klongs in every node of its path,
     * which the upward unlink (Dag.deleteUpward) can give to the node where the climb stops
     * (a bitmap, and with LE-b a klong of the empty key) and which also covers its time
     * klong; no node off the path, as the unlink, LE-b and root collapse change none. Root
     * collapse in a segment tree below a segment leaf L adds a klong to L for each level it
     * collapses (Dag.replaceRoot), several in one delete when a chain of single children
     * becomes the root (023-08, reviews B and C, 2.5): L gets one klong for each inner node
     * of each tree below L on the paths (023-11, review B, B1: summed over the trees; every
     * path of a tree has as many), once for the transaction, as each such collapse unlinks a
     * root that existed before it, one level lower each time (a root that a split of the
     * transaction made is taken back in place, with no klong). The space root's collapses
     * change the top node of the transaction, which Db counts.</li>
     * <li>the merges at a delete (bergdb 024-21; 024-11, CB1 and CB2): two klongs more in every
     * node of its path, four in all: a merge of a child gives the node at most three (a
     * bitmap, the left child's klong and a second new node's; a rule O of the child before
     * its merge gives a time split's klong, which the merge then points in place), and one
     * for the extra overflow of a merged node below (next); and four nodes for each level of
     * its path and two levels more, for new roots that splits of the transaction can make
     * above it: a delete merges at most once a level (fix climbs only after a merge into one
     * node), a merge makes at most two new nodes, and two more are for one extra overflow of
     * a merged node, a half and a new root, as a merged node holds the klongs of two
     * positions of the walk (its left and its right node), floor((a + b) / q) <= floor(a /
     * q) + floor(b / q) + 1. A merged node starts with up to c + 1 klongs, so a node of a
     * delete's path overflows as if it had at most q klongs of room (roomAfterReplacement).
     * A sibling that a merge leaves out is not made dirty. With m < 2 (minFill) there are
     * no merges, and these are counted as a margin. An argument, checked by DagTester's tests
     * of the bound (bergdb 024-11, TU8), not a proof. For node size 30 and a path of 5 nodes,
     * about 30 nodes a delete: a record's limit takes about 120,000 deletes in one
     * transaction; a larger one is refused (Db.checkDirtyNodes), as one of puts that can make
     * too many nodes dirty is.</li>
     * <li>option 2 of dead klongs (bergdb 024-23, 2.6): a node that holds d dead klongs and
     * gets k klongs with d + k > theta can be compacted, once, by a new node and a klong in its
     * parent, so it overflows at least once. Its replacement has no less room than the node
     * would have, so it overflows by its size no more often, and later compactions in the
     * transaction are of nodes the transaction made, in place: nothing more is counted.</li>
     * </ul>
     * 
     * @param deletes  deletes[i] is true if keys[i] is deleted; a delete of a missing key
     *      changes nothing.
     */
    public long dirtyNodeBound(long time, long[][] keys, boolean[] deletes, GetData gd) {
        return dirtyNodeBound(time, keys, deletes, gd, null);
    }
    
    /** As dirtyNodeBound; with 'klongsOut' not null, the klongs counted for each node walked,
     *  before the splits' klongs (for tests). */
    long dirtyNodeBound(long time, long[][] keys, boolean[] deletes, GetData gd,
            java.util.Map<KeyNode, Long> klongsOut) {
        final KeyNode root = topDs.findRoot(time, gd);
        if (root == null) {
            return 0;
        }
        final java.util.IdentityHashMap<KeyNode, Walked> walked =
                new java.util.IdentityHashMap<KeyNode, Walked>();
        final KlongWithPointer kwi = gd.kwi;
        boolean anyDelete = false;
        long mergeLevels = 0;           // the levels of the deletes' paths, two more each
        
        for (int k = 0; k < keys.length; k++) {
            final long[] key = keys[k];
            KeyNode node = root;
            Walked w = walked(walked, node, null);
            gd.descentFrom(node);
            for (int i = 0; i < key.length; i++) {
                while (!node.isSegmentLeaf()) {
                    node.searchLte(time, key[i], kwi);
                    if (kwi.klong == Klong.NULL) {
                        break;
                    }
                    node = (KeyNode) gd.followPointer(node, kwi.pointerIndex);
                    gd.descentTo(node);
                    w = walked(walked, node, w);
                }
                if (i == key.length - 1) {
                    if (deletes[k]) {
                        // The upward unlink, LE-b, root collapse and the merges (see above):
                        // four klongs in every node of the path, and the inner nodes of each
                        // segment tree on it, for the collapses, at the segment leaf above
                        // that tree; for the merges four nodes a level and two levels more.
                        anyDelete = true;
                        mergeLevels += w.depth + 1 + 2;
                        int inner = 0;
                        for (Walked u = w, below = null; u != null; below = u, u = u.up) {
                            u.klongs += 4;
                            u.deleteBelow = true;
                            if (u.node.isSegmentLeaf()) {
                                if (below != null) {        // 'below' is a tree's root
                                    below.collapses = Math.max(below.collapses, inner);
                                }
                                inner = 0;
                            } else {
                                inner++;
                            }
                        }
                    } else {
                        w.klongs++;
                    }
                    break;
                }
                node.searchEq(time, key[i], kwi);
                if (kwi.klong == Klong.NULL) {
                    if (!deletes[k]) {
                        w.fresh(key, i);
                    }
                    break;
                }
                node = (KeyNode) gd.followPointer(node, kwi.pointerIndex);
                gd.descentTo(node);
                w = walked(walked, node, w);
            }
        }
        
        long count = walked.size();
        if (anyDelete) {
            for (Walked w : walked.values()) {
                if (w.up != null) {
                    w.up.klongs += w.collapses;     // summed over the trees below a leaf
                }
            }
        }
        if (klongsOut != null) {
            for (Walked w : walked.values()) {
                klongsOut.put(w.node, w.klongs);
            }
        }
        final java.util.List<Walked> deepestFirst = new java.util.ArrayList<Walked>(walked.values());
        java.util.Collections.sort(deepestFirst, new java.util.Comparator<Walked>() {
            public int compare(Walked a, Walked b) {
                return Integer.compare(b.depth, a.depth);
            }
        });
        for (Walked w : deepestFirst) {
            if (w.freshKeys != null) {
                for (java.util.List<long[]> l : w.freshKeys.values()) {
                    count += freshTreeBound(l, w.freshLevel + 1);
                }
            }
            final long overflows = overflows(w.klongs, w.node.size, w.deleteBelow, w.dead);
            if (overflows > 0) {
                count += overflows + 1;
                if (w.up != null) {
                    w.up.klongs += overflows + 1;
                } else {
                    count += overflows;             // new roots
                }
            }
        }
        if (anyDelete) {
            count += 4 * mergeLevels;               // the merges (see above)
        }
        return count;
    }
    
    /** A node that dirtyNodeBound() walked. */
    private static final class Walked {
        final KeyNode node;
        final Walked up;                // the node above it on the path, null for the space root
        final int depth;
        long klongs = 0;                // that it gets
        int collapses = 0;              // root collapses of its tree at most, a tree's root
        boolean deleteBelow = false;    // a delete's path goes through it (merges)
        final int dead;                 // its dead klongs as walked (option 2)
        java.util.HashMap<Long, java.util.List<long[]>> freshKeys = null;
        int freshLevel;                 // the segment of the keys in freshKeys missing here
        
        Walked(KeyNode node, Walked up) {
            this.node = node;
            this.up = up;
            this.depth = up == null ? 0 : up.depth + 1;
            this.dead = deadCount(node);
        }
        
        /** A key whose segment i is not in this leaf: a new segment tree below it. */
        void fresh(long[] key, int i) {
            if (freshKeys == null) {
                freshKeys = new java.util.HashMap<Long, java.util.List<long[]>>();
                freshLevel = i;
            }
            java.util.List<long[]> l = freshKeys.get(key[i]);
            if (l == null) {
                l = new java.util.ArrayList<long[]>();
                freshKeys.put(key[i], l);
                klongs++;                       // the pointer to the new segment tree
            }
            l.add(key);
        }
    }
    
    private static Walked walked(java.util.IdentityHashMap<KeyNode, Walked> walked, KeyNode node,
            Walked up) {
        Walked w = walked.get(node);
        if (w == null) {
            w = new Walked(node, up);
            walked.put(node, w);
        }
        return w;
    }
    
    /**
     * How many times a node of 'size' klongs, given 'klongs' more and a TIME klong, can
     * overflow. 'merged': a delete's path goes through it, so a merge can replace it by a node
     * of up to c + 1 klongs, with at most q of room (bergdb 024-21).
     */
    private long overflows(long klongs, int size, boolean merged) {
        if (klongs == 0) {
            return 0;
        }
        return overflows(klongs, size, merged, -1);
    }
    
    /**
     * As overflows(klongs, size, merged) for a node of the tree that holds 'dead' dead klongs
     * (option 2, bergdb 024-23, 2.6): if its klongs can take it above theta, it can be
     * compacted, once, by a new node and a klong in its parent: one overflow at least. Its
     * replacement has no less room than the node would have, and later compactions in the
     * transaction are of nodes it made, in place. 'dead' < 0: a node of a new tree, none.
     */
    private long overflows(long klongs, int size, boolean merged, int dead) {
        if (klongs == 0) {
            return 0;
        }
        final int theta = theta(maxNodeSize);
        final long least = theta > 0 && dead >= 0 && dead + klongs > theta ? 1 : 0;
        final long k = klongs + 1;
        final long q = roomAfterReplacement();
        long room = Math.max(0, maxNodeSize - 2 - size);
        if (merged) {
            room = Math.min(room, q);
        }
        if (k <= room) {
            return least;
        }
        return 1 + (k - room - 1) / q;
    }
    
    /**
     * The nodes of the new segment trees of 'keys', which share their segments before 'level'
     * and whose segment 'level' is in a new tree: its root, the in-place splits of its new
     * nodes (one new node and one klong above a split), a new root for each level, and the
     * trees below.
     */
    private long freshTreeBound(java.util.List<long[]> keys, int level) {
        //
        // A loop over the trees, with a stack of the trees still to count, not a recursion
        // (bergdb 021-16): a new tree has a level per segment of 7 bytes of a key, and a put
        // of a key of 1,000,000 bytes after one of 100,000 with the same start overflowed the
        // thread's stack, which failed the database. The count is a sum, the same in any order.
        //
        long count = 0;
        final java.util.ArrayList<java.util.List<long[]>> trees =
                new java.util.ArrayList<java.util.List<long[]>>();
        final java.util.ArrayList<Integer> levels = new java.util.ArrayList<Integer>();
        trees.add(keys);
        levels.add(level);
        while (!trees.isEmpty()) {
            final java.util.List<long[]> treeKeys = trees.remove(trees.size() - 1);
            final int treeLevel = levels.remove(levels.size() - 1);
            long klongs = 0;
            java.util.HashMap<Long, java.util.List<long[]>> below =
                    new java.util.HashMap<Long, java.util.List<long[]>>();
            for (long[] key : treeKeys) {
                if (key.length == treeLevel + 1) {
                    klongs++;                       // a value
                } else {
                    java.util.List<long[]> l = below.get(key[treeLevel]);
                    if (l == null) {
                        l = new java.util.ArrayList<long[]>();
                        below.put(key[treeLevel], l);
                        klongs++;                   // the pointer to the tree below
                    }
                    l.add(key);
                }
            }
            count += 1;
            for (long ov = overflows(klongs, 0, false); ov > 0; ov = overflows(ov, 1, false)) {
                count += ov + 1;                    // the splits, and a new node above them
            }
            for (java.util.List<long[]> l : below.values()) {
                trees.add(l);
                levels.add(treeLevel + 1);
            }
        }
        return count;
    }
    
    // ======== getMany() ========
    
    /**
     * Get multiple KVs in increasing (or decreasing) key order.
     * 
     * @param g
     *            Input and output parameters. The GetMany object should have been createed
     *            with the newGetMany() factory method.
     * @see GetMany
     * @throws StreamFormatException
     *             If the database stream is corrupt.
     * @throws StreamIoException
     *             If there was an i/o error with the database stream.
     */
    public void getMany(GetMany g) {
        //
        // Note, multiple get operations may be running in parallel.
        // All data used must be thread safe. Temporary, operation-local data is stored in 
        // the 'g' object.
        //

        if (g.endKey != null && !g.forward) {
            // Refused before the root is looked up, also when there is none (bergdb 021-28).
            throw new IllegalArgumentException("g.endKey with a backward scan: the end is for "
                    + "forward scans only (bergdb 021-28).");
        }
        
        KeyNode root = topDs.findRoot(g.actualLookupTime, g.gd);
        
        if (root == null) {
            // No state at the lookup time, before the first transaction: the end at once, and
            // eod() says so, as StopCondition promises (bergdb 020-27; it was not called).
            g.stopCondition.eod();
            return;
        }

        GetMany.Chain chain = g.new Chain();
        chain.setup(root);

        outer: while (true) {
            Kvt kvt = chain.next();

            if (kvt == null) {
                g.stopCondition.eod();
                break outer;
            }
            
            g.getOpCount++;
            int shouldStop = g.stopCondition.handleKvt(kvt);

            switch (shouldStop) {
            case StopCondition.STOP:
                break outer;
            case StopCondition.ADD:
                g.result.add(kvt);
                break;
            case StopCondition.ADD_AND_STOP:
                g.result.add(kvt);
                break outer;
            case StopCondition.CONTINUE:
                // empty
                break;
            default:
                // The application's answer, refused (bergdb 020-27, Q2): an assert until then,
                // whose AssertionError with -ea failed the database (Db.getMany), and without
                // -ea the answer was taken as CONTINUE.
                throw new IllegalArgumentException("handleKvt() returned " + shouldStop
                        + ", not ADD, STOP, CONTINUE or ADD_AND_STOP.");
            }
        }
    }    
    

    // ======== putKv() with helpers ========
    
    /**
     * <p>Adds a KV to the graph.
     * If a value for the key exists, the previous value for the key is replaced.
     * If value is null, this is a delete operation.</p>
     * 
     * <p>This method runs with exclusive write access to the data structure 
     * (synchronized on Db.writeLock). However, there may be concurrent readers 
     * that read with a lookup time strictly less than the transaction time
     * of the current transaction.</p>
     * 
     * @param key     The key (as segments).
     * @param value   The value; null for delete operation.
     * @throws DbException
     */
    public void putKv(long[] key, byte[] value, PutData pd) {
        //
        // in:   time, key, value.
        // out:  changes to dag, 
        //       changed/new nodes reported to pd.nodeChangeListener.
        //       new pointers reported to pd.pointerCreatedListener.
        //
        // ALL modifications to the Dag are done through this method.
        // The call graph has recursion; appendKlongs() is called by successors of appendKlong()
        // on call graph.
        //
        
        assert pd.tt >= 0;
        assert pd.nodeChangeListener != null;
        assert pd.pointerListener != null;
        assert pd.pointerCreatedListener != null;
        assert key != null && key.length > 0 : "key not non-null and with length > 0";
        
        final KeyNode root = topDs.findRoot(pd.tt, pd);
        
        if (root == null) {
            throw new DbException("Found no root node at t=" + pd.tt + ", cannot continue put.");
        }
        
        KeyNode segmentRoot = root;
        final int segmentCount = key.length;
        final int lastSegment = segmentCount - 1;
        
        for (int i = 0; i < segmentCount; i++) {            
            if (i == lastSegment) {
                setValue(segmentRoot, key[i], key, value, pd);
            } else {
                segmentRoot = setNode(segmentRoot, key[i], value != null, pd);
                if (segmentRoot == null) {
                    // A delete of a key that does not exist, a noop. No node must be
                    // created; noops are not stored, so the rerun at startup would not
                    // create it, and node ids would differ after a restart.
                    return;
                }
            }
        }
    }
    
    /**
     * Sets a value in the segment that has 'node' as its root node. If a Kv
     * with the key already exists, its value is overwritten.
     * 
     * @param node
     *            The segment root node.
     */
    private void setValue(KeyNode node, long compareValue, long[] key, byte[] value, PutData pd) {
        assert node != null : "node is null";
        
        pd.descentFrom(node);
        while (!node.isSegmentLeaf()) {
            node.searchLte(pd.tt, compareValue, pd.kwi);
            checkFound(node, pd);
            
            node = (KeyNode) pd.followPointer(node, pd.kwi.pointerIndex);
            assert node != null;
            pd.descentTo(node);
        }

        if (value == null) {
            // A delete operation. A ValueNode (of delete type) is created
            // only for the pd.nodeChangeListener.
            
            boolean isNoop = deleteUpward(node, pd.keyAccessPath.size - 1, compareValue, key, pd);
            if (!isNoop) {
                pd.nodeChangeListener.valueNodeCreated(ValueNode.createDelete(), key);
            }
            
        } else {
            ValueNode valueNode = new ValueNode(value);
            pd.nodeChangeListener.valueNodeCreated(valueNode, key);
            
            // "+1" is needed. We need to be able to fit two more klongs. 
            // A TIME klong may be needed.
            
            if (node.size + 1 < this.maxNodeSize
                    && !deadFull(node, isLive(node, compareValue) ? 1 : 0)) {
                node.addKlong(pd.tt, Klong.compareValueToKeyKlong(compareValue),
                        valueNode, pd.accessData);
                pd.pointerCreatedListener.pointerCreated(node, node.size - 1, valueNode);
                pd.nodeChangeListener.keyNodeChanged(node);
            } else {
                pd.oneKwi[0].klong = Klong.compareValueToKeyKlong(compareValue);
                pd.oneKwi[0].node = valueNode;
                pd.oneKwi[0].pos = pd.accessData;
                appendKlongs(node, pd.keyAccessPath.size - 1, pd.oneKwi, pd);
            }
        }
    }
        
    /**
     * Ensures a klong-and-node with compareValue exists in the segment of the
     * data structure with 'segmentRoot' as the root node. If it does not exist,
     * a new klong is inserted pointing to a new node. The new node is the
     * segment root of a newly created segment. Returns the next segment root.
     * If 'create' is false, nothing is created and null is returned if the
     * node does not exist.
     */
    /**
     * A put finds a klong at or below its key in every key node on its way that is not a
     * segment leaf (the graph's invariant). A node from a damaged stream may have none
     * (2026-11-06, bergdb 019-32: a segment leaf's flag changed, its checksum right): the put
     * fails, and so the database, or the start's rerun, which refuses the stream. It was an
     * assert: an AssertionError, and without -ea the put followed another pointer.
     */
    private static void checkFound(KeyNode node, PutData pd) {
        if (pd.kwi.klong == Klong.NULL) {
            throw new DbException("Key node " + node.getId() + ", not a segment leaf, has no "
                    + "klong at or below the key at time " + pd.tt + ": corrupt data.");
        }
    }

    private KeyNode setNode(KeyNode segmentRoot, long compareValue, boolean create, PutData pd) {
        KeyNode current = segmentRoot;
        KeyNode result;
        
        assert current.assertOk(this.maxNodeSize);
        
        pd.descentFrom(current);
        while (!current.isSegmentLeaf()) {
            current.searchLte(pd.tt, compareValue, pd.kwi);
            checkFound(current, pd);
            assert pd.kwi.pointerIndex >= 0 
                    : "LTE search found klong, but pointerIndex=" + pd.kwi.pointerIndex;
            
            current = (KeyNode) pd.followPointer(current, pd.kwi.pointerIndex);
            pd.descentTo(current);
            assert current.assertOk(this.maxNodeSize);
        }
        
        current.searchEq(pd.tt, compareValue, pd.kwi);

        if (pd.kwi.klong == Klong.NULL && !create) {
            result = null;

        } else if (pd.kwi.klong == Klong.NULL) {
            // If not found, create the node

            KeyNode child = new KeyNode(true); // New segment leaf node.
            pd.nodeChangeListener.keyNodeCreated(child);
            
            // "+1" needed since there might be a need to insert a TIME klong too.
            if (current.size + 1 < this.maxNodeSize) {
                current.addKlong(pd.tt, Klong.compareValueToKeyKlong(compareValue),
                        child, pd.accessData);
                pd.pointerCreatedListener.pointerCreated(current, current.size-1, child);
                pd.nodeChangeListener.keyNodeChanged(current);
            } else {
                pd.oneKwi[0].klong = Klong.compareValueToKeyKlong(compareValue);
                pd.oneKwi[0].node = child;
                pd.oneKwi[0].pos = pd.accessData;
                appendKlongs(current, pd.keyAccessPath.size - 1, pd.oneKwi, pd);
            }
            
            result = child;
            
        } else {
            // If found
            result = (KeyNode) pd.followPointer(current, pd.kwi.pointerIndex);
        }

        return result;
    }
    

    /**
     * Appends a delete klong to 'node' if needed to delete the node with the
     * given compare value.
     * 
     * @return True if the operation is a noop (no operation).
     */
    private boolean appendDeleteKlong(final KeyNode node, final int depth,
            final long compareValueToDelete, PutData pd) {
        //
        // If needed, a delete bitmap klong is added to the node for the current
        // transaction time to delete a key klong with the specified compareValue.
        // If no such key klong exists, or if it is already deleted, no action
        // is taken (it is a NOOP).
        // If 'node' ends with a delete klong of the current transaction (same transaction time), 
        // said delete klong is updated to set a delete bit for the specified compareValue.
        //
        // -- Implementation notes --
        // Loop through. Is it a noop? If not, can it be added to existing
        // delete klong of transaction or not? At end if noop, do nothing. If not, either modify
        // existing delete klong or add one to 'node'.
        //

        final short sz = node.size;
        assert sz <= this.maxNodeSize : "Bad node size: " + sz;
        long arrayTime = -1;
        long tTime = pd.tt;
        long arrayDel = Klong.createDelete();
        long del = Klong.createDelete();
        boolean hasTransDel = false;
            // Set to true if last klong is a delete for the same time as this transaction.

        for (int i = 0; i < sz; i++) {
            long klong = node.klongs[i];
            int type = Klong.getIntType(klong);

            switch (type) {
            case Klong.INT_TYPE_TIME:
                arrayTime = Klong.getTime(klong);
                if (arrayTime > tTime) {
                    throw new Bug("Bad state of node, arrayTime > transaction time."
                            + " arrayTime=" + arrayTime + ", tTime=" + tTime + ", node="
                            + node.toString() + ".");
                }
                break;
            case Klong.INT_TYPE_KEY:
                long arrayCompareValue = Klong.getCompareValue(klong);
                if (compareValueToDelete == arrayCompareValue) {
                    del = Klong.delete(del, i);
                }
                break;
            case Klong.INT_TYPE_DELETE_BITMAP:
                arrayDel = klong;
                if (arrayTime == tTime && i == sz - 1) {
                    hasTransDel = true;
                }
                break;
            default:
                assert false : "Bad klong type at " + i + ": " + type + ".";
                break;
            }
        }

        long union = (del | arrayDel);
        boolean isNoop = (union == arrayDel);
        
        if (!isNoop) {
            if (hasTransDel && deadFull(node, 1)) {
                // The transaction's own bitmap would delete one klong too many (option 2).
                KeyNode last = node.lastVersionGivenDel(sz, tTime, union);
                handleFullNode(node, depth, ZERO_LONG_KWP, tTime, last, true, pd);
                
            } else if (hasTransDel) {
                node.klongs[sz - 1] = union;
                pd.nodeChangeListener.keyNodeChanged(node);
                
                // Direct modification, but still OK. A reader will always have a lookup
                // time < trans.transTime. So, a reader is guaranteed not to see
                // the delete at trans.transTime before the transaction completes.
                
            } else {                
                final boolean room = node.size + 1 < this.maxNodeSize;
                if (room && !deadFull(node, 1)) {
                    node.addDeleteKlong(tTime, union);
                    pd.nodeChangeListener.keyNodeChanged(node);
                } else {                    
                    KeyNode last = node.lastVersionGivenDel(sz, tTime, union);
                    handleFullNode(node, depth, ZERO_LONG_KWP, tTime, last, room, pd);
                }
            }
        }
        
        return isNoop;
    }
    
    
    // ======== The upward unlink at a delete (bergdb 023-05, P1) ========
    //
    // A delete that leaves its segment leaf with no live KEY klong at the transaction time tt
    // does not write the leaf: it deletes the parent's klong to it instead, and so on upward
    // while a node is left with no live klong, also across segment trees (an emptied segment
    // root takes the segment's klong in the segment leaf above). The first node that keeps a
    // live klong gets the delete. Frans's rule of 2012, "If lastVersion is empty, remove from
    // parent" (bergdb 020-30-02), for every emptied node (023-04, UP).
    //
    // Every inner node has the empty key (Klong.EMPTY_KEY, compare value 0) as its smallest
    // live klong (bergdb 023-04, LE-b; 023-05, P4): the roots that space splits make have it,
    // and a space split of an inner node gives its second half the empty key for its first
    // klong (KeyNode.firstAndSecond). So every klong above a leaf is a lower bound of every key
    // below it, and the empty key is the one every put relies on (checkFound). When the child
    // of the empty key empties, the empty key is pointed to the next live child, whose own
    // klong is deleted (emptyKeyNext): one klong in the node, which is on the delete's path,
    // and nothing below changes, as the next child's first klong is the empty key already.
    //
    // A node that the transaction made by a split (a last version, a half or a new root, its
    // first klong of tt) and that it empties is taken back (takeBack; 023-04, X5 (a)): never
    // written, as if never made, so that a transaction leaves no node it made unreachable at
    // its time (the Lean model's A3; handleFullNode). Any other node made by the transaction
    // holds only puts of the transaction, which one operation a key leaves live, so no delete
    // empties it (023-04, X5 (c)): a Bug (023-08, sections 5 and 7).
    //
    // An unlinked node gets no entry of tt and loses those it got earlier in the transaction
    // (toPreviousState, as a node replaced by a split), and is reported as replaced, so that
    // it leaves D if it got dirty in this transaction only (Db.endOfTrans): no lookup at tt or
    // later reaches it, lookups before tt still do, through the klong as it was. A space root
    // that is a segment leaf stays, empty; an inner one is never emptied, as root collapse
    // lowers it first (a Bug otherwise; bergdb 023-11, review A, S1).
    //
    // All of it is a function of the delete and the state at tt (the model's A1), so the
    // startup's rerun redoes it; a record of format 6 means it (StoredTrans.RECORD_FORMAT).
    //
    // Since format 7 (bergdb 024-21) a delete also merges underfull nodes (mergeAfterDelete,
    // below), so every key node but a root of a segment tree holds at least m >= 2 live
    // klongs (node size 8 and more): a delete empties only a root, and the climb above, the
    // take-back of an emptied half and LE-b's relabel are reached from an emptied root only:
    // the segment leaf above takes the delete, or the climb goes on above it when it is a root
    // that the delete empties too. A record of format 7 means the delete with the merges.
    //
    
    /** Counts for tests and measurements; written by the writer only. */
    public static volatile long statUnlinked, statClimbs, statRelabels,
            statKeptNew, statTakenBack, statCollapses, statRootsTakenBack;
    
    /**
     * A delete of 'compareValue', the key's last segment, in the segment leaf 'leaf' at
     * 'depth' of pd.keyAccessPath, with the upward unlink (see above).
     * 
     * @return True if the delete is a noop: the key has no live value.
     */
    private boolean deleteUpward(final KeyNode leaf, final int depth, final long compareValue,
            final long[] key, PutData pd) {
        final long tt = pd.tt;
        final long leafDel = lastBitmap(leaf);
        final long leafUnion = leafDel | bitsOf(leaf, compareValue);
        if (leafUnion == leafDel) {
            return true;
        }
        final int full0 = pd.fullNodes;
        final int roots0 = pd.newRootsMade;
        if (!allKeysIn(leaf, leafUnion)) {
            appendDeleteKlong(leaf, depth, compareValue, pd);
            if (mergeAfterDelete(key, depth, full0, roots0, pd)) {
                collapseRoot(key, key.length - 1, pd);
            }
            return false;
        }
        
        // The leaf is empty after the delete. Find 'stop', the node that gets the delete: the
        // first above that keeps a live klong. Nothing is changed until it is known, so a climb
        // that cannot go on changes nothing above the leaf.
        final KeyAccessPath path = pd.keyAccessPath;
        int top = depth;
        int stop;
        while (true) {
            final KeyNode n = path.get(top);
            if (n.getFirstTime() == tt && top > 0
                    && !canTakeBack(n, path.get(top - 1), path.getKlong(top), pd)) {
                // Made by this transaction, and not by a split of a node that existed (023-04,
                // X5 (c)): such a node, and every node below it, holds only puts of the
                // transaction, and a transaction reaches the Dag with one operation a key
                // (Db.transformKeys refuses a transaction whose key transformations make two
                // of its keys one key; bergdb 024-16; 023-08, section 7), so no delete of it
                // empties the node. Nothing is changed yet.
                // Until 2026-11-10 a segment leaf kept the delete here, reached through a
                // KeyTransformation's put and a delete of one key (023-08, section 3).
                throw new Bug("The upward unlink at " + tt + ": key node " + n.getId()
                        + ", made by the transaction and not by a split, is emptied: two"
                        + " operations on one key in a transaction (bergdb 023-08, X5 (c)).");
            }
            if (top == 0) {
                // The space root. A segment leaf stays, empty, with the delete, also one that
                // the transaction made. An inner one is never emptied: root collapse lowers an
                // inner root as soon as a climb leaves it one live klong, and a root that the
                // transaction made fresh holds only its puts (bergdb 023-11, review A, S1).
                if (!n.isSegmentLeaf()) {
                    throw new Bug("The upward unlink at " + tt + ": inner space root "
                            + n.getId() + " is emptied (bergdb 023-11, S1).");
                }
                if (n.getFirstTime() == tt) {
                    statKeptNew++;
                }
                stop = 0;
                break;
            }
            final KeyNode p = path.get(top - 1);
            final long c = Klong.getCompareValue(path.getKlong(top));
            if (allKeysIn(p, lastBitmap(p) | bitsOf(p, c))) {
                top--;
                continue;
            }
            stop = top - 1;
            break;
        }
        
        if (stop == depth) {
            appendDeleteKlong(leaf, depth, compareValue, pd);
            return false;
        }
        
        statClimbs++;
        
        // The segment of 'stop''s tree, from the path before it changes, for root collapse.
        int segment = 0;
        for (int i = 0; i < stop; i++) {
            if (path.get(i).isSegmentLeaf()) segment++;
        }
        
        for (int k = depth; k > stop; k--) {
            final KeyNode n = path.get(k);
            if (n.getFirstTime() == tt) {
                takeBack(n, path.get(k - 1), path.getKlong(k), pd);
            } else {
                unlink(n, pd);
            }
        }
        
        final KeyNode s = path.get(stop);
        final long c = Klong.getCompareValue(path.getKlong(stop + 1));
        
        if (s.isSegmentLeaf()) {
            appendDeleteKlong(s, stop, c, pd);
            if (mergeAfterDelete(key, stop, full0, roots0, pd)) {
                collapseRoot(key, segment, pd);
            }
            return false;
        }
        if (smallestLive(s) != 0) {
            throw new Bug("The upward unlink at " + tt + ": inner node " + s.getId()
                    + " has no live klong of the empty key (bergdb 023-04, LE-b).");
        }
        if (c != 0) {
            appendDeleteKlong(s, stop, c, pd);
        } else {
            // The leftmost child (023-04, LE-b).
            statRelabels++;
            emptyKeyNext(s, stop, pd);
        }
        mergeAfterDelete(key, stop, full0, roots0, pd);
        collapseRoot(key, segment, pd);
        return false;
    }
    
    /**
     * RC, root collapse (bergdb 023-04, 2.3; 023-05, P1), after a climb that ended in an inner
     * node of the tree of segment 'segment': while the root of that tree is an inner node,
     * not made by the transaction, with one live klong, its only child takes its place: for
     * the space root through a new super root (as time-split-2 makes one), for a segment root
     * through a klong with the same compare value in the segment leaf above, which shadows the
     * old one (as time-split-1 does for a segment root). The old root is unlinked (unlink). The
     * one live klong of a root is the empty key, and the child's smallest klong is the empty
     * key too, as every inner node's is (LE-b), or the child is a segment leaf.
     * The child does not change, so it is followed without being marked: the model marks it
     * only if something below it changed.
     * 
     * <p>A root that a split of the transaction made (a last version, or a new root above two
     * halves) is collapsed too, and taken back (023-05, P4): the klong of tt that links it,
     * in the top node of tt or in the segment leaf above, is pointed to the child instead,
     * behind the time klong of tt, where every reader stops; the root is reported as
     * replaced, so it is never written, as takeBack does. Before, such a root ended the
     * collapse: a full root replaced by a delete's bitmap in the transaction's last delete
     * kept a chain of single children (T3, "hashed", four levels).</p>
     */
    private void collapseRoot(long[] key, int segment, PutData pd) {
        final long tt = pd.tt;
        while (true) {
            final KeyNode root = descendToRootQuietly(key, segment, pd);
            if (root.isSegmentLeaf()) {
                return;
            }
            final boolean made = root.getFirstTime() == tt;
            if (made && pd.replacedBy(root) == null) {
                return;
            }
            final int only = onlyLiveKlong(root);
            if (only < 0) {
                return;
            }
            if (Klong.getCompareValue(root.klongs[only]) != 0) {
                throw new Bug("Root collapse at " + tt + ": the one live klong of root "
                        + root.getId() + " is not the empty key.");
            }
            if (made) {
                takeBackRoot(root, pd.keyAccessPath.size - 1, only, pd);
            } else {
                replaceRoot(root, pd.keyAccessPath.size - 1, only, pd);
            }
        }
    }
    
    /**
     * Root collapse of 'root', made by a split of the transaction, at 'depth' of
     * pd.keyAccessPath, whose one live child is that of its klong at 'only': the child takes
     * its place in the klong of tt that links it, and 'root' is taken back (see
     * collapseRoot).
     */
    private void takeBackRoot(KeyNode root, int depth, int only, PutData pd) {
        final long tt = pd.tt;
        final KeyNode child = followQuietly(root, only, pd);
        if (depth == 0) {
            // The top node of tt is updated in place (TopDs.newSuperRoot).
            topDs.newSuperRoot(tt, child, pd.accessData, pd.pointerCreatedListener,
                    pd.nodeChangeListener);
        } else {
            final KeyNode leaf = pd.keyAccessPath.get(depth - 1);
            final int i = linkIndex(leaf, root, pd.keyAccessPath.getKlong(depth));
            if (i < 0 || lastTime(leaf) != tt) {
                throw new Bug("Root collapse at " + tt + ": no klong of tt to root "
                        + root.getId() + " in its segment leaf.");
            }
            leaf.repointKlong(i, child);
            pd.nodeChangeListener.keyNodeChanged(leaf);
        }
        pd.nodeChangeListener.keyNodeTakenBack(root);
        statTakenBack++;
        statRootsTakenBack++;
        statCollapses++;
    }
    
    /**
     * One step of root collapse: 'root', at 'depth' of pd.keyAccessPath, is replaced by the
     * child of its klong at 'only', its one live child: the space root through a new super
     * root, a segment root through a klong with the same compare value in the segment leaf
     * above. The child is followed before 'root' is unlinked, as unlinking drops the klongs
     * of tt, and without being marked: it does not change.
     */
    private void replaceRoot(KeyNode root, int depth, int only, PutData pd) {
        final long tt = pd.tt;
        final KeyNode child = followQuietly(root, only, pd);
        if (depth == 0) {
            unlink(root, pd);
            topDs.newSuperRoot(tt, child, pd.accessData, pd.pointerCreatedListener,
                    pd.nodeChangeListener);
        } else {
            final KeyNode leaf = pd.keyAccessPath.get(depth - 1);
            final long klong = pd.keyAccessPath.getKlong(depth);
            unlink(root, pd);
            pd.oneKwi[0].klong = klong;
            pd.oneKwi[0].node = child;
            pd.oneKwi[0].pos = pd.accessData;
            appendKlongs(leaf, depth - 1, pd.oneKwi, pd);
        }
        statCollapses++;
    }
    
    /**
     * As descendToSegmentRoot(), but the segment root itself is followed without being marked
     * (followQuietly) and put on the key access path by hand: after a collapse it is the old
     * root's child, which does not change, and the model marks a node only if something below
     * it changed. The nodes above it are followed as by any descent: they are above the
     * climb's change, or the segment leaf above changed by the collapse.
     */
    private KeyNode descendToRootQuietly(long[] key, int segment, PutData pd) {
        final long tt = pd.tt;
        if (segment == 0) {
            pd.keyAccessPath.clearFast();
            final PointerListener listener = pd.pointerListener;
            pd.pointerListener = DO_NOTHING_POINTER_LISTENER;
            final KeyNode root;
            try {
                root = topDs.findRoot(tt, pd);
            } finally {
                pd.pointerListener = listener;
            }
            pd.keyAccessPath.add(Klong.NULL, root);
            return root;
        }
        final KlongWithPointer kwi = pd.kwi;
        KeyNode node = descendToSegmentRoot(key, segment - 1, pd);
        while (!node.isSegmentLeaf()) {
            node.searchLte(tt, key[segment - 1], kwi);
            checkFound(node, pd);
            node = (KeyNode) pd.followPointer(node, kwi.pointerIndex);
        }
        node.searchEq(tt, key[segment - 1], kwi);
        if (kwi.klong == Klong.NULL) {
            throw new Bug("Descent at " + tt + ": segment " + (segment - 1) + " not found.");
        }
        final long klong = kwi.klong;
        final KeyNode root = followQuietly(node, kwi.pointerIndex, pd);
        pd.keyAccessPath.add(klong, root);
        return root;
    }
    
    /** The index of the latest klong of the node's only live compare value; -1 if it has
     *  none or more than one. */
    private static int onlyLiveKlong(KeyNode node) {
        final long del = lastBitmap(node);
        int index = -1;
        long cv = -1;
        for (int i = 0; i < node.size; i++) {
            final long klong = node.klongs[i];
            if (Klong.getIntType(klong) != Klong.INT_TYPE_KEY || Klong.isDeleted(del, i)) {
                continue;
            }
            final long c = Klong.getCompareValue(klong);
            if (index >= 0 && c != cv) {
                return -1;
            }
            index = i;
            cv = c;
        }
        return index;
    }
    
    /** Follows pointer 'index' of 'node' as the writer, without telling pd's listener: the
     *  node is not marked, nor put on the key access path. */
    private static KeyNode followQuietly(KeyNode node, int index, PutData pd) {
        final PointerListener listener = pd.pointerListener;
        pd.pointerListener = DO_NOTHING_POINTER_LISTENER;
        try {
            return (KeyNode) pd.followPointer(node, index);
        } finally {
            pd.pointerListener = listener;
        }
    }
    
    /**
     * Goes down from the space root at tt by the key's segments before 'segment' to the root
     * of that segment's tree, and returns it. Rebuilds pd.keyAccessPath.
     */
    private KeyNode descendToSegmentRoot(long[] key, int segment, PutData pd) {
        final long tt = pd.tt;
        final KlongWithPointer kwi = pd.kwi;
        pd.keyAccessPath.clearFast();
        KeyNode node = topDs.findRoot(tt, pd);
        for (int i = 0; i < segment; i++) {
            while (!node.isSegmentLeaf()) {
                node.searchLte(tt, key[i], kwi);
                checkFound(node, pd);
                node = (KeyNode) pd.followPointer(node, kwi.pointerIndex);
            }
            node.searchEq(tt, key[i], kwi);
            if (kwi.klong == Klong.NULL) {
                throw new Bug("Descent at " + tt + ": segment " + i + " not found.");
            }
            node = (KeyNode) pd.followPointer(node, kwi.pointerIndex);
        }
        return node;
    }
    
    /**
     * Unlinks 'node', which existed before the transaction, at tt: it loses its klongs of tt
     * and is reported as replaced (see above).
     */
    private void unlink(KeyNode node, PutData pd) {
        assert node.getFirstTime() != pd.tt : "unlink of a node made in the transaction";
        if (lastTime(node) == pd.tt) {
            node.toPreviousState(pd.tt - 1);
        }
        pd.nodeChangeListener.keyNodeReplaced(node);
        statUnlinked++;
    }
    
    /**
     * True if 'node', made by this transaction and linked by its klong 'klong' of tt in
     * 'parent', replaces a node that existed before (a split's last version, half or new
     * root), so that it can be taken back (takeBack).
     */
    private boolean canTakeBack(KeyNode node, KeyNode parent, long klong, PutData pd) {
        return pd.replacedBy(node) != null && linkIndex(parent, node, klong) >= 0;
    }
    
    /** The index of the live klong of 'parent' with the compare value of 'klong' that points
     *  to 'node', or -1. */
    private static int linkIndex(KeyNode parent, KeyNode node, long klong) {
        final long cv = Klong.getCompareValue(klong);
        final long del = lastBitmap(parent);
        for (int i = parent.size - 1; i >= 0; i--) {
            final long k = parent.klongs[i];
            if (Klong.getIntType(k) == Klong.INT_TYPE_KEY && Klong.getCompareValue(k) == cv) {
                return !Klong.isDeleted(del, i) && parent.getPointerNode(i) == node ? i : -1;
            }
        }
        return -1;
    }
    
    /**
     * Takes back 'node', made by this transaction by a split and emptied in it (bergdb 023-04,
     * X5 (a); 023-05, P1): its parent's klong of tt to it, and every other klong of tt there
     * that names it, deleted ones too (retarget), is pointed to the node it replaced, which
     * existed before the transaction and is not current, so nothing points to 'node' any
     * more; the climb then deletes that klong in the parent, or points it to the next child
     * if it is the empty key's (emptyKeyNext), as for any emptied child. The klongs are behind
     * the parent's time klong of tt, where every reader stops, as replaceKlong changes such
     * klongs. 'node' is reported as replaced, so it leaves
     * D and is never written: as far as the stream and the model see, it was never made.
     */
    private void takeBack(KeyNode node, KeyNode parent, long klong, PutData pd) {
        final KeyNode old = pd.replacedBy(node);
        if (old == null || linkIndex(parent, node, klong) < 0 || lastTime(parent) != pd.tt) {
            throw new Bug("Take back of key node " + node.getId() + " at " + pd.tt
                    + ": no node it replaces, or no klong of tt to it.");
        }
        // The live klong of tt to it, and any deleted one: the next child's own klong after
        // emptyKeyNext pointed the empty key to it (bergdb 023-07, section 5.1, fault 6).
        retarget(parent, node, old, pd.tt);
        pd.nodeChangeListener.keyNodeTakenBack(node);
        statTakenBack++;
    }
    
    /**
     * Points every KEY klong of tt in 'p' (behind its time klong of tt, where every reader
     * stops) that points to 'from', a node that the transaction made and takes back, to 'to':
     * no written node may point to a node that is never written, not even by a deleted klong
     * (bergdb 023-05, P5; 023-07, section 5.1).
     */
    private static void retarget(KeyNode p, KeyNode from, KeyNode to, long tt) {
        if (lastTime(p) != tt) {
            return;
        }
        for (int i = p.size - 1; i >= 0; i--) {
            final long klong = p.klongs[i];
            if (Klong.getIntType(klong) == Klong.INT_TYPE_TIME) {
                break;
            }
            if (Klong.getIntType(klong) == Klong.INT_TYPE_KEY && p.getPointerNode(i) == from) {
                p.repointKlong(i, to);
            }
        }
    }
    
    /**
     * LE-b, the empty key first (bergdb 023-04, 2.2 and X1; 023-05, P4). The child of the
     * empty key of the inner node 'node', at 'depth' of pd.keyAccessPath, its leftmost child,
     * has emptied: the empty key is pointed to the next live child, the one with the smallest
     * live compare value but the empty key's, and that child's compare value is deleted. A
     * new klong of the empty key, with a copy of the child's pointer, shadows the old one, as
     * a time split's klong does. If the latest klong of the empty key is of tt (a split of the
     * transaction made it, or a take-back or an earlier call pointed it), it is pointed to the
     * next child in place instead: it is behind the time klong of tt, where every reader
     * stops, as replaceKlong changes such klongs. Nothing below changes: the next child's own
     * first klong is the empty key already (KeyNode.firstAndSecond), or it is a segment leaf.
     * A full node is replaced by its last version, with the empty key instead of the next
     * child's klong (the order stays sorted), through handleFullNode with no klong to insert;
     * so is a node that would hold more than theta dead klongs (option 2, deadFull).
     */
    private void emptyKeyNext(final KeyNode node, final int depth, PutData pd) {
        assert !node.isSegmentLeaf();
        final long tt = pd.tt;
        final short sz = node.size;
        long arrayDel = Klong.DELETE_NONE_BITMAP;
        long arrayTime = -1;
        int timeIndex = -1;
        boolean hasTransDel = false;
        int e = -1;                         // the latest klong of the empty key
        for (int i = 0; i < sz; i++) {
            final long klong = node.klongs[i];
            switch (Klong.getIntType(klong)) {
            case Klong.INT_TYPE_TIME:
                arrayTime = Klong.getTime(klong);
                timeIndex = i;
                break;
            case Klong.INT_TYPE_DELETE_BITMAP:
                arrayDel = klong;
                hasTransDel = arrayTime == tt && i == sz - 1;
                break;
            default:
                if (Klong.getCompareValue(klong) == 0) {
                    e = i;
                }
                break;
            }
        }
        // The next live child: the smallest live compare value but the empty key's, and its
        // latest klong.
        final long del0 = arrayDel | bitsOf(node, 0);
        int j = -1;
        long jcv = -1;
        for (int i = 0; i < sz; i++) {
            final long klong = node.klongs[i];
            if (Klong.getIntType(klong) != Klong.INT_TYPE_KEY || Klong.isDeleted(del0, i)) {
                continue;
            }
            final long cv = Klong.getCompareValue(klong);
            if (j == -1 || cv <= jcv) {
                j = i;
                jcv = cv;
            }
        }
        if (e == -1 || Klong.isDeleted(arrayDel, e) || j == -1) {
            throw new Bug("LE-b at " + tt + " in key node " + node.getId() + ": "
                    + (j == -1 ? "no next child." : "no live klong of the empty key."));
        }
        final long union = arrayDel | bitsOf(node, jcv);
        final boolean inPlace = arrayTime == tt && e > timeIndex;
        final int need = (hasTransDel ? 0 : 1) + (inPlace ? 0 : 1) + (arrayTime == tt ? 0 : 1);
        final boolean room = sz + need <= this.maxNodeSize;
        
        // The dead klongs it adds: the next child's klong, and the empty key's unless in place.
        // Not reached at format 7 from node size 8 (every node but a root holds m >= 2 live
        // klongs, so no delete empties an inner node's child; theta is 0 below 8): the Lean
        // model's emptyKeyNext runs it (treetest, theta forced below 8; bergdb 024-23, R3).
        if (room && !deadFull(node, inPlace ? 1 : 2)) {
            // The bitmap first: in the model's terms a bitmap deletes the klongs before it with
            // the compare values of its new bits (docs/trace-format.md, "D"); the empty key is
            // not one of them, so the order is free.
            if (hasTransDel) {
                node.klongs[sz - 1] = union;    // the transaction's own bitmap, no reader sees it
            } else {
                node.addDeleteKlong(tt, union);
            }
            final int index;
            if (inPlace) {
                node.copyPointer(e, j);
                index = e;
            } else {
                index = node.addKlongCopyPointer(tt, Klong.EMPTY_KEY, j);
            }
            final Node pointee = node.getPointerNode(index);
            if (pointee != null) {
                pd.pointerCreatedListener.pointerCreated(node, index, pointee);
            }
            pd.nodeChangeListener.keyNodeChanged(node);
        } else {
            final KeyNode last = node.lastVersionGivenDel(sz, tt, del0);
            assert Klong.getType(last.klongs[0]) == Klong.TYPE_TIME;
            if (last.size < 2 || Klong.getCompareValue(last.klongs[1]) != jcv) {
                throw new Bug("LE-b at " + tt + " in key node " + node.getId()
                        + ": the last version does not start with the next child.");
            }
            last.klongs[1] = Klong.EMPTY_KEY;   // sorted still: the empty key is below the rest
            handleFullNode(node, depth, ZERO_LONG_KWP, tt, last, room, pd);
        }
    }
    
    /** The last delete bitmap of the node, or one with no bit set. */
    private static long lastBitmap(KeyNode node) {
        final short sz = node.size;
        long del = Klong.DELETE_NONE_BITMAP;
        for (int i = 0; i < sz; i++) {
            final long klong = node.klongs[i];
            if (Klong.getIntType(klong) == Klong.INT_TYPE_DELETE_BITMAP) {
                del = klong;
            }
        }
        return del;
    }
    
    /** The time of the node's last time klong, -1 if none. */
    private static long lastTime(KeyNode node) {
        for (int i = node.size - 1; i >= 0; i--) {
            final long klong = node.klongs[i];
            if (Klong.getIntType(klong) == Klong.INT_TYPE_TIME) {
                return Klong.getTime(klong);
            }
        }
        return -1;
    }
    
    /** The delete bits of every KEY klong of the node with the compare value. */
    private static long bitsOf(KeyNode node, long compareValue) {
        final short sz = node.size;
        long del = Klong.createDelete();
        for (int i = 0; i < sz; i++) {
            final long klong = node.klongs[i];
            if (Klong.getIntType(klong) == Klong.INT_TYPE_KEY
                    && Klong.getCompareValue(klong) == compareValue) {
                del = Klong.delete(del, i);
            }
        }
        return del;
    }
    
    /**
     * True if every KEY klong of the node is deleted by 'del': no compare value is live, as a
     * delete sets the bits of every klong of its compare value.
     */
    private static boolean allKeysIn(KeyNode node, long del) {
        final short sz = node.size;
        for (int i = 0; i < sz; i++) {
            if (Klong.getIntType(node.klongs[i]) == Klong.INT_TYPE_KEY && !Klong.isDeleted(del, i)) {
                return false;
            }
        }
        return true;
    }
    
    /** The smallest live compare value of the node, at the latest time; -1 if none. */
    private static long smallestLive(KeyNode node) {
        final long del = lastBitmap(node);
        final short sz = node.size;
        long best = -1;
        for (int i = 0; i < sz; i++) {
            final long klong = node.klongs[i];
            if (Klong.getIntType(klong) == Klong.INT_TYPE_KEY && !Klong.isDeleted(del, i)) {
                final long cv = Klong.getCompareValue(klong);
                if (best == -1 || cv < best) best = cv;
            }
        }
        return best;
    }
    
    

    // ======== Format 7's fill rule: the thresholds (bergdb 024-21; 024-11, section 5.1) ========
    //
    // The thresholds of a key node's fill, each a function of the node size B (maxNodeSize,
    // which the database's meta block holds). They are rules of record format 7
    // (StoredTrans.RECORD_FORMAT): a start reruns a record's puts and deletes with them, so a
    // change of any of them is a change of the format, and of every database's tree. Frans
    // decided them on 2026-11-11 at 14:34 (bergdb 024-14, QT1: the set m8, 8/17/17 for B =
    // 30); until then prototype P5's 7/15/15 (023-05). Another node size B gets v * B / 30 by
    // integer division, m at least 2, as 024-14's measuring build scaled them (QT2, other
    // node sizes, open): 2/4/4 at 8 and 3/7/7 at 14 (P5's), 16/35/35 at 62. Each is used only
    // through the three methods below.
    //

    /** The node size of the three values below; another node size scales them. */
    static final int THRESHOLDS_NODE_SIZE = 30;

    /**
     * h at node size 30: rule O (handleFullNode) replaces a full node by its last version, a
     * time split, if that holds at most h klongs with its time klong, else splits it in two
     * halves, a space split, each of at least h / 2 live klongs. 2026.4: B / 2, 15.
     */
    static final int SPLIT_ABOVE_30 = 17;

    /**
     * m at node size 30: after every transaction, every reachable key node that is not the
     * root of a segment tree holds at least m live klongs (bergdb 024-11, BU1 and V1); a delete
     * that leaves one with m - 1 merges it (mergeAfterDelete).
     */
    static final int MIN_FILL_30 = 8;

    /** c at node size 30: the most live klongs that a merge puts in one new node; more make
     *  two new nodes of about half each (a redistribution). */
    static final int MERGE_CAP_30 = 17;

    /**
     * The smallest node size with merges. Below it a space split's halves can hold fewer
     * than 2 live klongs (h / 2 < 2), so V1 cannot hold with m = 2: m is 1 there, and no node
     * is merged, as in 2026.4. A database has node size 8, 14, 30 or 62 (DbBuilder); smaller
     * ones are for Dag's own tests.
     */
    static final int MERGE_MIN_NODE_SIZE = 8;

    /** h for node size 'b' (see SPLIT_ABOVE_30): b / 2 below 8 too, as in 2026.4. */
    public static int splitAbove(int b) {
        return SPLIT_ABOVE_30 * b / THRESHOLDS_NODE_SIZE;
    }

    /** m for node size 'b' (see MIN_FILL_30, MERGE_MIN_NODE_SIZE). */
    public static int minFill(int b) {
        return b < MERGE_MIN_NODE_SIZE ? 1
                : Math.max(2, MIN_FILL_30 * b / THRESHOLDS_NODE_SIZE);
    }

    /** c for node size 'b' (see MERGE_CAP_30). */
    public static int mergeCap(int b) {
        return MERGE_CAP_30 * b / THRESHOLDS_NODE_SIZE;
    }

    /**
     * The room for more klongs that a node made by rule O or by a merge has at least, less a
     * margin of 3, and at least 2: q = max(2, min(B / 2, B - h, B - c) - 3), 10 at node size
     * 30. A time split's last version holds at most h klongs, a space split's half at most B /
     * 2, a merged node at most c + 1 (dirtyNodeBound; bergdb 024-14's count for its sets).
     */
    private int roomAfterReplacement() {
        final int b = maxNodeSize;
        return Math.max(2, Math.min(b / 2, Math.min(b - splitAbove(b), b - mergeCap(b))) - 3);
    }


    // ======== Option 2 of dead klongs: compaction at the write (bergdb 024-23; 024-18) ========
    //
    // A key node holds at most theta dead KEY klongs (deadCount: deleted by the node's last
    // bitmap, or followed by a later KEY klong of the same compare value). Before the writer
    // applies a write to a key node, it takes the dead klongs that the write adds: a put's
    // klong 1 if its key is live in the node (isLive), else 0; a delete's bitmap, new or the
    // transaction's own changed in place, 1; LE-b's bitmap and empty key 2, or 1 when the empty
    // key is pointed in place; a merge's parent 1 or 2; a split's klongs in the parent and
    // root collapse's klong 1 for each of a live compare value; a new segment's klong and a
    // klong pointed in place 0. If the node would then hold more than theta, it is full
    // (deadFull), and rule O replaces it by its last version with the write applied
    // (handleFullNode with 'compaction'): always one node, a time split, as the node had room
    // for the write and its last version has no more klongs; a node that the transaction made
    // is compacted in place. A node without room is full by its size first, as before. So after
    // every write a node holds at most theta dead klongs (bergdb 024-23, TP39), where the
    // merges alone allow B; and reclaim's rewrites, which are puts, compact the cold leaves
    // that they take above theta. A compaction keeps every live klong, so it changes no node's
    // fill (V1, BU1).
    // A function of the node and the write, so a start's rerun of a record of format 7 makes
    // the same nodes; no field (bergdb 024-23, sections 2.2 to 2.4; Frans's decision of
    // 2026-11-11, 024-18, QD1). The Lean model: Exec.lean's deadOver.
    //

    /** theta at node size 30 (Frans, 2026-11-11; bergdb 024-18, QD1). */
    static final int THETA_30 = 7;

    /**
     * theta for node size 'b': THETA_30 * b / 30 by integer division, at least 1, from node size
     * 8 (1 at 8, 3 at 14, 14 at 62); 0, off, below it, where format 7 merges nothing either
     * (bergdb 024-23, OD2; other node sizes are open with 024-14's QT2). A rule of record
     * format 7, as the thresholds are.
     */
    public static int theta(int b) {
        return b < MERGE_MIN_NODE_SIZE ? 0 : Math.max(1, THETA_30 * b / THRESHOLDS_NODE_SIZE);
    }

    /** Compactions made by option 2; written by the writer only. */
    public static volatile long statCompactions;

    /**
     * The dead KEY klongs of the node at the latest time: deleted by its last bitmap, or
     * followed by a later KEY klong of the same compare value; each once (bergdb 024-23, 2.1).
     */
    public static int deadCount(KeyNode node) {
        return deadCount(node, Integer.MAX_VALUE);
    }

    /** As deadCount(node), but the count stops at 'limit'. */
    private static int deadCount(KeyNode node, int limit) {
        final short sz = node.size;
        final long del = lastBitmap(node);
        int dead = 0;
        A: for (int i = 0; i < sz && dead < limit; i++) {
            final long klong = node.klongs[i];
            if (Klong.getIntType(klong) != Klong.INT_TYPE_KEY) {
                continue;
            }
            if (Klong.isDeleted(del, i)) {
                dead++;
                continue;
            }
            final long cv = Klong.getCompareValue(klong);
            for (int j = i + 1; j < sz; j++) {
                final long k2 = node.klongs[j];
                if (Klong.getIntType(k2) == Klong.INT_TYPE_KEY && Klong.getCompareValue(k2) == cv) {
                    dead++;
                    continue A;
                }
            }
        }
        return dead;
    }

    /** True if the compare value's latest KEY klong in the node is not deleted by its last
     *  bitmap: a klong of it added now shadows a live one. */
    private static boolean isLive(KeyNode node, long compareValue) {
        for (int i = node.size - 1; i >= 0; i--) {
            final long klong = node.klongs[i];
            if (Klong.getIntType(klong) == Klong.INT_TYPE_KEY
                    && Klong.getCompareValue(klong) == compareValue) {
                return !Klong.isDeleted(lastBitmap(node), i);
            }
        }
        return false;
    }

    /**
     * Option 2: a write that adds 'dead' dead klongs to 'node' would leave it with more than
     * theta: the node is full. Never with theta 0. A node of n klongs holds at most n - 1 KEY
     * klongs, so a small one is not counted.
     */
    private boolean deadFull(KeyNode node, int dead) {
        final int theta = theta(maxNodeSize);
        if (theta == 0 || node.size - 1 + dead <= theta) {
            return false;
        }
        return deadCount(node, theta - dead + 1) + dead > theta;
    }


    // ======== Merges at the delete (bergdb 024-21; 024-11, MG and section 5; 023-05, P5) ========
    //
    // Frans's plan of 2012: "Merges are made when the current version of a node shrinks
    // because of a delete"; the multiversion B-tree's weak version condition. After a delete
    // has changed a node X (its segment leaf; or after the upward unlink, which with merges
    // starts only at a root that the delete empties, the segment leaf above), fix(X): while X
    // is not the root of its segment tree and holds m - 1 live klongs at tt (minFill), it is
    // merged with a sibling S under its parent P: the child of P's live klong next below X's
    // if the two hold at most c live klongs together (mergeCap), else the child of the next
    // one above, else the one below (M1). L and R are the left and the right of the two.
    // Their live klongs at tt, in order, make one new node if they are at most c, else two
    // new nodes of half each, the first the larger (M3). P's klong of L points to the first
    // new node, R's compare value is deleted by a bitmap of tt before any new klong, and a
    // second new node gets a klong of its first compare value, or R's klong if that is the
    // same (M4). With the empty key first in every inner node (LE-b), R's empty key becomes
    // R's compare value in P in the merged node, and a second inner node starts with the
    // empty key, as a space split's second half does. A merge into one node takes a live
    // klong from P, so P is fixed in turn; a merge into two ends the loop. Then root
    // collapse (collapseRoot, F1): a root left with one live child gives way to it.
    //
    // The new nodes are last versions of tt, as a time split makes. L and R get no entry of
    // tt (M5): one that existed before is unlinked as a split's replaced node, so lookups
    // before tt still read it through P's old klongs, and it is written still if it was
    // dirty from an earlier transaction; one that the transaction made is taken back: every
    // klong of tt in P that names it is pointed to the first new node first, behind P's time
    // klong of tt, where every reader stops, and it is never written (keyNodeTakenBack).
    // The new nodes' pointers are copies of L's and R's while both are current (the model's
    // A-COPY): the same pointees, handles included.
    //
    // A function of the delete and the state at tt (the model's A1, 024-11's V9): the start's
    // rerun of a record of format 7 makes the same merges and the same nodes, in the same
    // order, reading the sibling as the writer did.
    //

    /** Counts for tests and measurements; written by the writer only. */
    public static volatile long statMerges, statMergesTwo, statMergeLeaves, statMergeTaken,
            statSiblingFollows, statSiblingLoads, statMergeKlongs,
            statMergeDup, statMergeMadeL, statMergeMadeR, statMergeDescents;

    /**
     * fix (bergdb 024-11, section 5.2, step 3) after a delete changed the node at 'depth' of
     * pd.keyAccessPath: merges it if it is not a root and holds fewer than m live klongs,
     * then its parent if that lost a live klong, and so on (see above). 'full0' and 'roots0'
     * are pd's counts before the change: a node replaced by rule O makes the path stale, so
     * it is walked again, and every new root that a space split made since is above the node
     * (splits go up the key's path only), so it moves the node's depth one down.
     *
     * @return True if a merge was made: then root collapse is due.
     */
    private boolean mergeAfterDelete(long[] key, int depth, int full0, int roots0,
            PutData pd) {
        final int m = minFill(maxNodeSize);
        if (m < 2) {
            return false;
        }
        boolean merged = false;
        boolean fresh = pd.fullNodes == full0;
        int d = depth + (pd.newRootsMade - roots0);
        while (d > 0) {
            final KeyNode x = fresh ? pd.keyAccessPath.get(d) : descendToDepth(key, d, pd);
            final KeyNode p = pd.keyAccessPath.get(d - 1);
            if (p.isSegmentLeaf() || liveCount(x, m) >= m) {
                break;          // a root of a segment tree, or not underfull (F3)
            }
            final int roots = pd.newRootsMade;
            final int r = merge(x, d, pd);
            merged = true;
            if (r == 2) {
                break;          // two new nodes: P keeps its count
            }
            fresh = false;
            d = d - 1 + (pd.newRootsMade - roots);
        }
        return merged;
    }

    /**
     * Goes down from the space root at tt along 'key' until pd.keyAccessPath has 'depth' + 1
     * nodes, and returns the last. The nodes are followed as by any descent, marked: every one
     * is an ancestor of the delete's change, or the node that took it.
     */
    private KeyNode descendToDepth(long[] key, int depth, PutData pd) {
        final long tt = pd.tt;
        final KlongWithPointer kwi = pd.kwi;
        final KeyAccessPath path = pd.keyAccessPath;
        statMergeDescents++;
        path.clearFast();
        KeyNode node = topDs.findRoot(tt, pd);
        int segment = 0;
        while (path.size - 1 < depth) {
            if (!node.isSegmentLeaf()) {
                node.searchLte(tt, key[segment], kwi);
                checkFound(node, pd);
            } else {
                node.searchEq(tt, key[segment], kwi);
                if (kwi.klong == Klong.NULL) {
                    throw new Bug("Merge descent at " + tt + ": segment " + segment
                            + " not found.");
                }
                segment++;
            }
            node = (KeyNode) pd.followPointer(node, kwi.pointerIndex);
        }
        if (path.size - 1 != depth || path.get(depth) != node) {
            throw new Bug("Merge descent at " + tt + ": the path is not as followed.");
        }
        return node;
    }

    /**
     * Merges the node 'x' at 'd' of pd.keyAccessPath, not a root of a segment tree, with its
     * sibling (see above; bergdb 024-11, section 5.3).
     *
     * @return 1: one new node, the parent lost a live klong; 2: two new nodes, the parent's
     *      live klongs are as many as before. A state that V1 to V3 exclude (no sibling, an
     *      empty node, an inner node without the empty key first) is a Bug (bergdb 024-21,
     *      section 6; 024-22, MD2): prototype P5 skipped the merge, and left the node under m.
     */
    private int merge(final KeyNode x, final int d, PutData pd) {
        final long tt = pd.tt;
        final int c = mergeCap(maxNodeSize);
        final KeyAccessPath path = pd.keyAccessPath;
        final KeyNode p = path.get(d - 1);
        final boolean inner = !x.isSegmentLeaf();
        final long cx = Klong.getCompareValue(path.getKlong(d));

        // x's klong in p, and the live klongs next above and below it (the latest of each).
        final long del = lastBitmap(p);
        final short sz = p.size;
        int ix = -1, ia = -1, ib = -1;
        long cva = 0, cvb = 0;
        for (int i = 0; i < sz; i++) {
            final long klong = p.klongs[i];
            if (Klong.getIntType(klong) != Klong.INT_TYPE_KEY || Klong.isDeleted(del, i)) {
                continue;
            }
            final long cv = Klong.getCompareValue(klong);
            if (cv == cx) {
                ix = i;
            } else if (cv > cx) {
                if (ia < 0 || cv <= cva) { ia = i; cva = cv; }
            } else {
                if (ib < 0 || cv >= cvb) { ib = i; cvb = cv; }
            }
        }
        final Node atX = ix < 0 ? null : p.getPointerNode(ix);
        if (ix < 0 || (atX != null && atX != x && atX.getId() != x.getId())) {
            throw new Bug("Merge at " + tt + ": key node " + x.getId() + " is not the live "
                    + "child of its klong in " + p.getId() + ".");
        }
        if (ia < 0 && ib < 0) {
            // A node that is not a root has a sibling (V2: an inner root holds 2 live klongs,
            // root collapse keeps it so; V1 any other inner node m >= 2).
            throw new Bug("Merge at " + tt + ": key node " + x.getId() + " has no sibling in "
                    + p.getId() + " (bergdb 024-11, V1 and V2).");
        }

        // M1, the sibling: the left one if both fit in one node (so that the nodes a run of
        // deletes in key order leaves behind fill up to c, as a twin's do), else the right
        // one, else the left one.
        KeyNode s = null;
        boolean right = true;
        if (ib >= 0) {
            final KeyNode left = sibling(p, ib, inner, pd);
            if (ia < 0 || liveCount(left, c + 1) + liveCount(x, c + 1) <= c) {
                s = left;
                right = false;
            }
        }
        if (s == null) {
            s = sibling(p, ia, inner, pd);
        }
        final KeyNode l = right ? x : s;
        final KeyNode r = right ? s : x;
        final int il = right ? ix : ib;
        final int ir = right ? ia : ix;
        final long klongL = p.klongs[il];
        final long klongR = p.klongs[ir];
        if (klongsOf(p, Klong.getCompareValue(klongL)) > 1
                || klongsOf(p, Klong.getCompareValue(klongR)) > 1) {
            statMergeDup++;     // two klongs of one compare value in the parent
        }
        if (l.getFirstTime() == tt) statMergeMadeL++;
        if (r.getFirstTime() == tt) statMergeMadeR++;

        // M2: the two last versions, read while both are current (A-COPY).
        final KeyNode lvL = l.lastVersion(tt);
        final KeyNode lvR = r.lastVersion(tt);
        final int nL = lvL.size - 1;
        final int nR = lvR.size - 1;
        final int n = nL + nR;
        if (nL == 0 || nR == 0 || (inner && (Klong.getCompareValue(lvL.klongs[1]) != 0
                || Klong.getCompareValue(lvR.klongs[1]) != 0))) {
            // An empty node that is not a root, or an inner node without the empty key first:
            // states that V1 and V3 (LE-b) exclude.
            throw new Bug("Merge at " + tt + ": key node " + l.getId() + " (" + nL + " live) or "
                    + r.getId() + " (" + nR + " live) is empty, or an inner node without the "
                    + "empty key first (bergdb 024-11, V1 and V3).");
        }

        // M3, the new nodes: one of n live klongs, or two, the first of the ceiling of half.
        final boolean two = n > c;
        final int k = two ? (n + 1) / 2 : n;
        final KeyNode m1 = new KeyNode(!inner);
        final KeyNode m2 = two ? new KeyNode(!inner) : null;
        m1.addToEnd(Klong.createTime(tt), null, Spos.NULL);
        if (two) m2.addToEnd(Klong.createTime(tt), null, Spos.NULL);
        long secondKlong = Klong.NULL;
        for (int j = 0; j < n; j++) {
            final KeyNode lv = j < nL ? lvL : lvR;
            final int i = j < nL ? j + 1 : j - nL + 1;
            long klong = lv.klongs[i];
            if (inner && lv == lvR && i == 1) {
                klong = klongR;             // the right node's empty key: its bound in p
            }
            if (two && j == k) {
                secondKlong = klong;
                if (inner) klong = Klong.EMPTY_KEY;
            }
            (j < k ? m1 : m2).addToEnd(klong, lv.getPointee(i), lv.getPointerPos(i));
        }

        assert m1.checkWithMessage() == null : m1.checkWithMessage();
        assert !two || m2.checkWithMessage() == null : m2.checkWithMessage();
        pd.nodeChangeListener.keyNodeCreated(m1);
        pd.madeFor(m1, l.getFirstTime() == tt ? pd.replacedBy(l) : l);
        reportNewPointers(m1, pd.pointerCreatedListener);
        pd.nodeChangeListener.keyNodeChanged(m1);
        if (two) {
            pd.nodeChangeListener.keyNodeCreated(m2);
            pd.madeFor(m2, r.getFirstTime() == tt ? pd.replacedBy(r) : r);
            reportNewPointers(m2, pd.pointerCreatedListener);
            pd.nodeChangeListener.keyNodeChanged(m2);
        }

        // M4, the parent.
        mergeParent(p, d - 1, il, klongL, m1, ir, klongR, m2, secondKlong, pd);

        // M5: l and r are left out: a node that existed before is unlinked (no entry of tt),
        // one that the transaction made is taken back, its klongs of tt in p pointed to m1
        // first.
        for (KeyNode o : new KeyNode[] {l, r}) {
            if (o.getFirstTime() == tt) {
                retarget(p, o, m1, tt);
                pd.nodeChangeListener.keyNodeTakenBack(o);
                statMergeTaken++;
            } else {
                unlink(o, pd);
            }
        }

        statMerges++;
        if (two) statMergesTwo++;
        if (!inner) statMergeLeaves++;
        statMergeKlongs += n;
        return two ? 2 : 1;
    }

    /**
     * The sibling at pointer 'index' of 'p', read as the writer reads a path (from the stream
     * if not resident), but not marked: it is left out if merged, and stays as it is if not
     * (bergdb 023-05, P1's fault 2).
     */
    private static KeyNode sibling(KeyNode p, int index, boolean inner, PutData pd) {
        final boolean resident = p.getPointerNode(index) != null;
        final KeyNode s = followQuietly(p, index, pd);
        statSiblingFollows++;
        if (!resident) statSiblingLoads++;
        if (s == null || s.isSegmentLeaf() == inner) {
            throw new Bug("Merge at " + pd.tt + ": the sibling at " + index + " of key node "
                    + p.getId() + " is not a node of its kind.");
        }
        return s;
    }

    /**
     * M4, the parent's change of a merge: 'p', at 'depth' of pd.keyAccessPath, gets its left
     * child's klong (at 'il') pointed to 'm1', and its right child's (at 'ir') deleted, or,
     * if 'm2' starts at the right child's compare value, pointed to 'm2'; else 'm2' gets a new
     * klong 'secondKlong'. The bitmap comes before any new klong (bergdb 023-06, section 6). A
     * klong of tt behind p's time klong of tt is pointed in place, as replaceKlong changes such
     * klongs. A full node is replaced by its last version with the new pointers set, through
     * handleFullNode with no klong to insert (rule O), so that a space split puts each in its
     * half; so is a node that would hold more than theta dead klongs (option 2, deadFull).
     */
    private void mergeParent(final KeyNode p, final int depth, final int il, final long klongL,
            final KeyNode m1, final int ir, final long klongR, final KeyNode m2,
            final long secondKlong, PutData pd) {
        final long tt = pd.tt;
        final long cR = Klong.getCompareValue(klongR);
        final boolean deleteR = m2 == null || Klong.getCompareValue(secondKlong) != cR;
        final short sz = p.size;
        long arrayTime = -1;
        int timeIndex = -1;
        long arrayDel = Klong.DELETE_NONE_BITMAP;
        boolean hasTransDel = false;
        for (int i = 0; i < sz; i++) {
            final long klong = p.klongs[i];
            switch (Klong.getIntType(klong)) {
            case Klong.INT_TYPE_TIME:
                arrayTime = Klong.getTime(klong);
                timeIndex = i;
                break;
            case Klong.INT_TYPE_DELETE_BITMAP:
                arrayDel = klong;
                hasTransDel = arrayTime == tt && i == sz - 1;
                break;
            default:
                break;
            }
        }
        final long union = deleteR ? arrayDel | bitsOf(p, cR) : arrayDel;
        final boolean lInPlace = arrayTime == tt && il > timeIndex;
        final boolean rInPlace = !deleteR && arrayTime == tt && ir > timeIndex;
        final int need = (deleteR && !hasTransDel ? 1 : 0) + (lInPlace ? 0 : 1)
                + (m2 == null || rInPlace ? 0 : 1) + (arrayTime == tt ? 0 : 1);
        final boolean room = sz + need <= this.maxNodeSize;
        // The dead klongs it adds: the right child's klong deleted or shadowed (unless pointed
        // in place), the left child's shadowed (unless pointed in place); a second new node's
        // klong of a new compare value adds none.
        final int dead = (deleteR ? 1 : 0) + (lInPlace ? 0 : 1)
                + (m2 != null && !deleteR && !rInPlace ? 1 : 0);

        if (room && !deadFull(p, dead)) {
            if (deleteR) {
                if (hasTransDel) {
                    p.klongs[sz - 1] = union;   // the transaction's own bitmap, no reader sees it
                } else {
                    p.addDeleteKlong(tt, union);
                }
            }
            link(p, il, klongL, m1, lInPlace, pd);
            if (m2 != null) {
                link(p, ir, deleteR ? secondKlong : klongR, m2, rInPlace, pd);
            }
            pd.nodeChangeListener.keyNodeChanged(p);
        } else {
            final KeyNode last = p.lastVersionGivenDel(sz, tt, union);
            if (!last.replaceKlong(tt, klongL, m1, pd.accessData)) {
                throw new Bug("Merge at " + tt + ": no klong of the left child in the last "
                        + "version of " + p.getId() + ".");
            }
            if (m2 != null) {
                if (!deleteR) {
                    if (!last.replaceKlong(tt, klongR, m2, pd.accessData)) {
                        throw new Bug("Merge at " + tt + ": no klong of the right child in "
                                + "the last version of " + p.getId() + ".");
                    }
                } else {
                    last.addSortedKlong(secondKlong, m2, pd.accessData);
                }
            }
            handleFullNode(p, depth, ZERO_LONG_KWP, tt, last, room, pd);
        }
    }

    /** Points p's klong at 'index' to 'node' in place, or adds a klong 'klong' to it. */
    private static void link(KeyNode p, int index, long klong, KeyNode node, boolean inPlace,
            PutData pd) {
        if (inPlace) {
            p.repointKlong(index, node);
            pd.pointerCreatedListener.pointerCreated(p, index, node);
        } else {
            p.addKlong(pd.tt, klong, node, pd.accessData);
            pd.pointerCreatedListener.pointerCreated(p, p.size - 1, node);
        }
    }

    /** The number of KEY klongs of the node with the compare value, live or not. */
    private static int klongsOf(KeyNode node, long compareValue) {
        int n = 0;
        for (int i = 0; i < node.size; i++) {
            final long klong = node.klongs[i];
            if (Klong.getIntType(klong) == Klong.INT_TYPE_KEY
                    && Klong.getCompareValue(klong) == compareValue) {
                n++;
            }
        }
        return n;
    }

    /**
     * The number of live compare values of the node at the latest time, counted up to
     * 'limit' (a merge's measure).
     */
    private static int liveCount(KeyNode node, int limit) {
        final long del = lastBitmap(node);
        final short sz = node.size;
        int count = 0;
        A: for (int i = 0; i < sz && count < limit; i++) {
            final long klong = node.klongs[i];
            if (Klong.getIntType(klong) != Klong.INT_TYPE_KEY || Klong.isDeleted(del, i)) {
                continue;
            }
            final long cv = Klong.getCompareValue(klong);
            for (int j = i + 1; j < sz; j++) {
                final long k2 = node.klongs[j];
                if (Klong.getIntType(k2) == Klong.INT_TYPE_KEY && !Klong.isDeleted(del, j)
                        && Klong.getCompareValue(k2) == cv) {
                    continue A;
                }
            }
            count++;
        }
        return count;
    }


    // ======== BU1's check (bergdb 024-21; 024-11, BU1, V1, V2, V4 and TU2) ========

    /** What checkFill() found: the counts of the walk, and the first violation or null. */
    public static final class Fill {
        /** Key nodes reachable at the time, segment trees, live keys, live klongs of the
         *  segment leaves (n + S - 1), and nodes that are not roots with fewer than m. */
        public long keyNodes, trees, liveKeys, leafKlongs, underfull;
        /** The dead klongs of the nodes (deadCount), summed, and the most of one node. */
        public long deadKlongs, deadMax;
        /** The first violation of V1, V2, V4, TU2's count or TP39, or null. */
        public String error;

        public String toString() {
            return "key nodes " + keyNodes + ", trees " + trees + ", live keys " + liveKeys
                    + ", leaf klongs " + leafKlongs + ", underfull " + underfull
                    + ", dead klongs " + deadKlongs + " (at most " + deadMax + " a node)"
                    + (error == null ? "" : ", " + error);
        }
    }

    /**
     * BU1's check: walks every key node reachable at 'time' (the latest time, for the bound)
     * through the live klongs, the latest of each compare value, and checks (bergdb 024-11,
     * section 2.4 and 5.4): V1, every key node that is not the root of a segment tree holds at
     * least m live klongs (minFill); V2, an inner root at least 2, a leaf root at least 1 but
     * the space root; V4, the leaves of a segment tree are at one depth; and TU2, the key
     * nodes are at most S + (n + S - 1) / (m - 1) for S segment trees and n live keys, which
     * V1, V2 and V4 give; and TP39 of option 2 (bergdb 024-23), every node holds at most
     * theta dead klongs (deadCount, at the latest time). For tests: it reads as a reader at
     * 'time' does, loading nodes through gd's follower. With m < 2 (node size below
     * MERGE_MIN_NODE_SIZE) it checks V2 and V4, and V1 as "not empty".
     */
    public Fill checkFill(long time, GetData gd) {
        final Fill f = new Fill();
        final int m = minFill(maxNodeSize);
        final int theta = theta(maxNodeSize);
        final KeyNode spaceRoot = topDs.findRoot(time, gd);
        if (spaceRoot == null) {
            return f;
        }
        // A stack of frames: the node, its depth in its segment tree, whether it is a root,
        // and its tree's leaf depth (-1 until its first leaf).
        final ArrayDeque<Object[]> todo = new ArrayDeque<Object[]>();
        todo.push(new Object[] {spaceRoot, 0, Boolean.TRUE, new int[] {-1}});
        f.trees = 1;
        while (!todo.isEmpty()) {
            final Object[] fr = todo.pop();
            final KeyNode node = (KeyNode) fr[0];
            final int depth = (Integer) fr[1];
            final boolean isRoot = (Boolean) fr[2];
            final int[] leafDepth = (int[]) fr[3];
            f.keyNodes++;
            final int dead = deadCount(node);
            f.deadKlongs += dead;
            f.deadMax = Math.max(f.deadMax, dead);
            if (theta > 0 && dead > theta && f.error == null) {
                f.error = "TP39: " + what(node, isRoot, depth) + " holds " + dead
                        + " dead klongs, more than theta = " + theta;
            }
            final int sz = node.size;
            final long del = node.getDeleteBitmapAtTime(time, sz);
            final java.util.TreeMap<Long, Integer> live = new java.util.TreeMap<Long, Integer>();
            for (int i = 0; i < sz; i++) {
                final long k = node.klongs[i];
                if (Klong.getIntType(k) == Klong.INT_TYPE_TIME && Klong.getTime(k) > time) {
                    break;
                }
                if (Klong.getIntType(k) != Klong.INT_TYPE_KEY || Klong.isDeleted(del, i)) {
                    continue;
                }
                live.put(Klong.getCompareValue(k), i);      // the latest of a compare value
            }
            final int cnt = live.size();
            if (!isRoot && cnt < m) {
                f.underfull++;
                if (f.error == null) {
                    f.error = "V1: " + what(node, isRoot, depth) + " holds " + cnt + " live klongs, fewer than m = "
                            + m;
                }
            }
            if (isRoot && f.error == null) {
                if (!node.isSegmentLeaf() && cnt < 2) {
                    f.error = "V2: inner root " + what(node, isRoot, depth) + " holds " + cnt + " live klongs";
                } else if (node != spaceRoot && cnt < 1) {
                    f.error = "V2: " + what(node, isRoot, depth) + " holds no live klong";
                }
            }
            if (node.isSegmentLeaf()) {
                if (leafDepth[0] < 0) {
                    leafDepth[0] = depth;
                } else if (leafDepth[0] != depth && f.error == null) {
                    f.error = "V4: " + what(node, isRoot, depth) + " is a leaf at another depth than "
                            + leafDepth[0];
                }
                for (int i : live.values()) {
                    f.leafKlongs++;
                    final long k = node.klongs[i];
                    if (Klong.getLength(k) < Klong.MAX_SIZE) {
                        f.liveKeys++;
                        continue;
                    }
                    f.trees++;
                    final KeyNode child = (KeyNode) gd.followPointer(node, i);
                    todo.push(new Object[] {child, 0, Boolean.TRUE, new int[] {-1}});
                }
            } else {
                for (int i : live.values()) {
                    final KeyNode child = (KeyNode) gd.followPointer(node, i);
                    todo.push(new Object[] {child, depth + 1, Boolean.FALSE, leafDepth});
                }
            }
        }
        if (f.error == null && m >= 2 && f.keyNodes > f.trees + f.leafKlongs / (m - 1)) {
            f.error = "TU2: " + f.keyNodes + " key nodes, more than S + (n + S - 1) / (m - 1) = "
                    + (f.trees + f.leafKlongs / (m - 1)) + " for S = " + f.trees + ", m = " + m;
        }
        return f;
    }
    
    
    private static String what(KeyNode node, boolean isRoot, int depth) {
        return "key node " + node.getId() + " (" + (node.isSegmentLeaf() ? "leaf" : "inner")
                + (isRoot ? ", a root" : "") + ", depth " + depth + " in its segment tree)";
    }
    
    
    // ======== appendKlongs() and helpers ========
    
    /**
     * Inserts one or two non-delete klongs to 'node' for the current
     * transaction. This method splits 'node' and its ancestors if needed.
     * 
     * @param node
     *            Node into which to insert.
     * @param depth
     *            Depth of 'node' in the access path.
     * @param toAppend
     *            The klongs, pointers, accessData to insert. 1 or 2 long array.
     */
    private void appendKlongs(final KeyNode node, final int depth, 
            final KlongWithPointer[] toAppend, PutData pd) {
        //
        // This should be the only way the db adds klongs to KeyNodes. It is the
        // central point of code for node splitting.
        //
        // Recursion is used, this method is called from methods called directly or 
        // indirectly from this method (method call graph has directed cycles).
        //
        // Implementation note: we allow memory allocation for a split, avoid it otherwise.
        // 

        assert toAppend.length < 3 : "toAppend.length = " + toAppend.length;
        assert toAppend.length > 0 : "toAppend.length = " + toAppend.length;
        assert node.assertOk(maxNodeSize);

        // "+1" is needed since a TIME klong could be added along with the toInsert klongs.
        final boolean sizeFull = node.size + toAppend.length + 1 > this.maxNodeSize;
        boolean compaction = false;
        if (!sizeFull) {
            int dead = 0;                       // the dead klongs the klongs add (option 2)
            for (int i = 0; i < toAppend.length; i++) {
                if (isLive(node, Klong.getCompareValue(toAppend[i].klong))) dead++;
            }
            compaction = deadFull(node, dead);
        }

        if (!sizeFull && !compaction) {
            for (int i = 0; i < toAppend.length; i++) {
                KlongWithPointer kwi = toAppend[i];
                node.addKlong(pd.tt, kwi.klong, kwi.node, pd.accessData);
                if (kwi.node != null) {
                    pd.pointerCreatedListener.pointerCreated(node, node.size - 1, kwi.node);
                }
            }
            pd.nodeChangeListener.keyNodeChanged(node);
            assert node.assertOk(maxNodeSize);
            
        } else {
            // 'node' is full. We cannot append 'toInsert' to it.
            // It is either space-full or time-full.
            //
            // 'last' is created, but note this is not always a node
            // that will be used in the DAG. If 'node' is space-full, 
            // 'first' and 'second' nodes will be used instead.
            // Therefore, pd.nodeChangeListener.keyNodeCreated()
            // is not called here for 'last'.
            //
            
            KeyNode last = node.lastVersion(pd.tt);
            
            assert last.assertOk(maxNodeSize);
            handleFullNode(node, depth, toAppend, pd.tt, last, compaction, pd);
        }
    }
    
    /**
     * This is an important method.
     * If last.size > splitAbove(maxNodeSize), h, then 'node' is split into two nodes -
     * a space-split is made. Otherwise, 'node' is replaced by the last version 
     * of it - a time-split.
     * 
     * <p>A node that the current transaction created is not replaced: it is split in place
     * (timeSplitInPlace, spaceSplitInPlace). A node that existed before is replaced, and then
     * loses the klongs of the current transaction, which its replacement has. So a
     * transaction leaves no node that it created unreachable at its time, and no klong of
     * its time in a node that is not reachable at that time: a whole transaction is one
     * transaction of the Lean model (assumptions A2 and A3; bergdb 011-11,
     * M1). Before 2026-10-16, a later key of a transaction could replace a node that an
     * earlier key had created or changed.</p>
     * 
     * <p>'compaction': the node had room for the write, and is full by its dead klongs only
     * (option 2, deadFull): it is replaced by its last version with the write applied, a time
     * split, whatever h says. The last version holds no more klongs than the node with the
     * write would, so it fits (bergdb 024-23, 2.2).</p>
     */
    private void handleFullNode(final KeyNode node, final int depth,
            final KlongWithPointer[] toInsert, final long tTime, KeyNode last,
            final boolean compaction, PutData pd) {
        //
        // When this method is called, 'last' has not been added reported as a new node
        // (pd.nodeChangeListener.keyNodeChanged(last) not called).
        //
        // A node with no klong before tTime was created by this transaction (or was empty
        // before it). No reader can see its klongs: readers use lookup times before tTime,
        // and it is linked only by klongs of tTime. So it can be changed in place.
        //
        
        final boolean newInTrans = node.getFirstTime() == tTime;
        
        pd.fullNodes++;                 // the key access path may be stale now (merges)
        if (compaction) {
            statCompactions++;
            if (last.size + toInsert.length > this.maxNodeSize) {
                throw new Bug("Compaction at " + tTime + " of key node " + node.getId()
                        + ": its last version and the write do not fit (bergdb 024-23, 2.2).");
            }
        }
        
        if (!compaction && last.size > splitAbove(this.maxNodeSize)) {
            if (newInTrans) {
                spaceSplitInPlace(node, last, depth, toInsert, pd);
            } else {
                spaceSplit(node, last, depth, toInsert, pd);
            }
        } else {
            if (newInTrans) {
                timeSplitInPlace(tTime, node, last, toInsert, pd);
            } else {
                pd.madeFor(last, node);
                timeSplit(tTime, last, depth, toInsert, pd);
            }
        }
        
        if (!newInTrans) {
            // 'node' is no longer current. Its klongs of tTime are in its replacement
            // ('last' copies every live klong), and no reader sees them (lookup times are
            // before tTime), so they go: otherwise the node would keep klongs that no lookup
            // ever sees. See the class comment of KeyNode about the size of a replaced node.
            node.toPreviousState(tTime - 1);
            pd.nodeChangeListener.keyNodeReplaced(node);
        }
    }
    
    /**
     * A time split of a node that the current transaction created: the node is compacted
     * in place to its last version, instead of being replaced by it. See handleFullNode().
     */
    private void timeSplitInPlace(final long tTime, final KeyNode node, KeyNode last,
            KlongWithPointer[] toAppend, PutData pd) {
        for (int i = 0; i < toAppend.length; i++) {
            KlongWithPointer kwi = toAppend[i];
            boolean replaced = last.replaceKlong(tTime, kwi.klong, kwi.node, pd.accessData);
            if (!replaced) last.addKlong(tTime, kwi.klong, kwi.node, pd.accessData);
        }
        
        node.setContentFrom(last);
        reportNewPointers(node, pd.pointerCreatedListener);
        pd.nodeChangeListener.keyNodeChanged(node);
        pd.splitListener.nodeSplit(Dag.TIME_SPLIT_1);
        assert node.checkWithMessage() == null : node.checkWithMessage();
    }
    
    /**
     * A space split of a node that the current transaction created: the node keeps the first
     * half, in place, and only the second half is a new node. A space root or a segment root
     * gets a new root above both halves, as in spaceSplit(). See handleFullNode().
     */
    private void spaceSplitInPlace(final KeyNode node, KeyNode last, final int depth,
            final KlongWithPointer[] toInsert, PutData pd) {
        final long tt = pd.tt;
        final boolean isSegmentLeaf = node.isSegmentLeaf();
        final KeyNode first = new KeyNode(isSegmentLeaf);     // only holds the first half
        final KeyNode second = new KeyNode(isSegmentLeaf);
        final KeyNode parent = pd.getParent(depth);
        
        pd.nodeChangeListener.keyNodeCreated(second);
        pd.madeFor(second, pd.replacedBy(node));
        long secondKlong = node.firstAndSecond(tt, last, toInsert, first, second);
        node.setContentFrom(first);
        reportNewPointers(node, pd.pointerCreatedListener);
        reportNewPointers(second, pd.pointerCreatedListener);
        pd.nodeChangeListener.keyNodeChanged(node);
        pd.nodeChangeListener.keyNodeChanged(second);
        
        if (parent == null || parent.isSegmentLeaf()) {
            // 'node' is the space root or a segment root: a new root above both halves.
            pd.newRootsMade++;
            KeyNode newRoot = new KeyNode(false);
            pd.nodeChangeListener.keyNodeCreated(newRoot);
            pd.madeFor(newRoot, pd.replacedBy(node));
            newRoot.addKlong(tt, Klong.EMPTY_KEY, node, pd.accessData);
            pd.pointerCreatedListener.pointerCreated(newRoot, newRoot.size - 1, node);
            newRoot.addKlong(tt, secondKlong, second, pd.accessData);
            pd.pointerCreatedListener.pointerCreated(newRoot, newRoot.size - 1, second);
            
            if (parent == null) {
                topDs.newSuperRoot(tt, newRoot, pd.accessData, pd.pointerCreatedListener,
                        pd.nodeChangeListener);
                pd.splitListener.nodeSplit(Dag.SPACE_SPLIT_3);
            } else {
                // The segment leaf's klong of tt to 'node' is pointed to newRoot in place, as
                // TopDs.newSuperRoot does for the space root: a second klong would shadow it
                // and still name 'node', and if the transaction then empties 'node' and takes
                // it back, which points klongs in its parent only (takeBack, retarget,
                // takeBackRoot), a written node would name a node never written (bergdb
                // 023-08, review C, fault 12). The klong is behind the leaf's time klong of tt,
                // where every reader stops, as replaceKlong changes such klongs.
                final long klong1 = pd.keyAccessPath.getKlong(depth);
                assert klong1 != Klong.NULL : "Missing klong in keyAccessPath, " + depth;
                final int i = linkIndex(parent, node, klong1);
                if (i < 0 || lastTime(parent) != tt) {
                    throw new Bug("Space split at " + tt + ": no klong of tt to segment root "
                            + node.getId() + " in its segment leaf.");
                }
                parent.repointKlong(i, newRoot);
                pd.pointerCreatedListener.pointerCreated(parent, i, newRoot);
                pd.nodeChangeListener.keyNodeChanged(parent);
                pd.splitListener.nodeSplit(Dag.SPACE_SPLIT_2);
            }
            assert newRoot.checkWithMessage() == null;
        } else {
            // The parent already points to 'node', the first half.
            pd.oneKwi[0].klong = secondKlong;
            pd.oneKwi[0].node = second;
            pd.oneKwi[0].pos = pd.accessData;
            appendKlongs(parent, depth - 1, pd.oneKwi, pd);
            pd.splitListener.nodeSplit(Dag.SPACE_SPLIT_1);
        }
    }
    
    /**
     * A time split "replaces" the time-full node with the last version of it.
     * This method handles both: time-split-1 and time-split-2 cases.
     */
    private void timeSplit(final long tTime, KeyNode last, final int depth,
            KlongWithPointer[] toAppend, PutData pd) {
        //
        // 131005, added the last.replaceKlong() method call. A bit of a hack.
        //   See DagTester.testTimeSplit1a().
        //   NOTE Consider other solution. Maybe last should include toAppend.
        //
        // Last version is small enough not to split into two nodes, but not empty.
        //
                
        final KeyNode parent = pd.getParent(depth);

        for (int i = 0; i < toAppend.length; i++) {
            KlongWithPointer kwi = toAppend[i];    
            boolean replaced = last.replaceKlong(tTime, kwi.klong, kwi.node, pd.accessData);
            if (!replaced) last.addKlong(tTime, kwi.klong, kwi.node, pd.accessData);
        }
        
        pd.nodeChangeListener.keyNodeCreated(last);
        reportNewPointers(last, pd.pointerCreatedListener);
        
        if (parent == null) {
            // time-split-2:
            // No parent, 'last' is the new super root.
            
            topDs.newSuperRoot(tTime, last, pd.accessData, pd.pointerCreatedListener, pd.nodeChangeListener);
            
            pd.splitListener.nodeSplit(Dag.TIME_SPLIT_2);
            assert last.checkWithMessage() == null;
            
        } else {
            // time-split-1:
            // There is a parent.
            
            long klong1 = pd.keyAccessPath.getKlong(depth);
            assert klong1 != Klong.NULL : "time-split-1, missing klong in keyAccessPath, " + depth;

            pd.oneKwi[0].klong = klong1;
            pd.oneKwi[0].node = last;
            pd.oneKwi[0].pos = pd.accessData;
            
            appendKlongs(parent, depth - 1, pd.oneKwi, pd);
            
            pd.splitListener.nodeSplit(Dag.TIME_SPLIT_1);
            assert parent.checkWithMessage() == null : parent.checkWithMessage() + " node:\n"
                    + parent.print();
        }
    }
    
    /**
     * Called to space split 'node'.
     * There are three kinds of space splits:
     * space-split-1: The node is not a segment root.
     * space-split-2: The node is a segment root (parent is segment leaf).
     * space-split-3: The node is the space root node (parent == null).
     * 
     * @param node    The node that is full and needs to be split.
     * @param last    The last version of 'node'.
     * @param depth   The current depth in the tree, used together with pd.getParent().
     * @param toInsert  Klongs to insert.
     */
    private void spaceSplit(final KeyNode node, KeyNode last, final int depth,
            final KlongWithPointer[] toInsert, PutData pd) {
        final long tt = pd.tt;
        final boolean isSegmentLeaf = node.isSegmentLeaf();
        final KeyNode first = new KeyNode(isSegmentLeaf);
        final KeyNode second = new KeyNode(isSegmentLeaf);
        final KeyNode parent = pd.getParent(depth);

        pd.nodeChangeListener.keyNodeCreated(first);
        pd.nodeChangeListener.keyNodeCreated(second);
        pd.madeFor(first, node);
        pd.madeFor(second, node);
        
        if (parent == null) {
            //
            // space-split-3:
            // 'node' is the space root node.
            //
            pd.newRootsMade++;
            KeyNode newRoot = new KeyNode(false);
            pd.nodeChangeListener.keyNodeCreated(newRoot);
            pd.madeFor(newRoot, node);
            
            long secondKlong = node.firstAndSecond(tt, last, toInsert, first, second);
            reportNewPointers(first, pd.pointerCreatedListener);
            reportNewPointers(second, pd.pointerCreatedListener);
            
            newRoot.addKlong(tt, Klong.EMPTY_KEY, first, pd.accessData);
            pd.pointerCreatedListener.pointerCreated(newRoot, newRoot.size - 1, first);
            newRoot.addKlong(tt, secondKlong, second, pd.accessData);
            pd.pointerCreatedListener.pointerCreated(newRoot, newRoot.size - 1, second);
            
            pd.nodeChangeListener.keyNodeChanged(first);
            pd.nodeChangeListener.keyNodeChanged(second);

            topDs.newSuperRoot(tt, newRoot, pd.accessData, pd.pointerCreatedListener, pd.nodeChangeListener);

            pd.splitListener.nodeSplit(Dag.SPACE_SPLIT_3);
            assert newRoot.checkWithMessage() == null;

        } else if (parent.isSegmentLeaf()) {
            //
            // space-split-2:
            // 'node' is a segment root since parent is a segment leaf.
            //
            
            pd.newRootsMade++;
            KeyNode newSegmentRoot = new KeyNode(false);
            pd.nodeChangeListener.keyNodeCreated(newSegmentRoot);
            pd.madeFor(newSegmentRoot, node);
            long secondKlong = node.firstAndSecond(tt, last, toInsert, first, second);
            reportNewPointers(first, pd.pointerCreatedListener);
            reportNewPointers(second, pd.pointerCreatedListener);
            
            newSegmentRoot.addKlong(tt, Klong.EMPTY_KEY, first, pd.accessData);
            pd.pointerCreatedListener.pointerCreated(newSegmentRoot, newSegmentRoot.size - 1, first);
            newSegmentRoot.addKlong(tt, secondKlong, second, pd.accessData);
            pd.pointerCreatedListener.pointerCreated(newSegmentRoot, newSegmentRoot.size - 1, second);
            
            pd.nodeChangeListener.keyNodeChanged(first);
            pd.nodeChangeListener.keyNodeChanged(second);

            long klong1 = pd.keyAccessPath.getKlong(depth);
            assert klong1 != Klong.NULL : "Missing klong in keyAccessPath, " + depth;

            pd.oneKwi[0].klong = klong1;
            pd.oneKwi[0].node = newSegmentRoot;
            pd.oneKwi[0].pos = pd.accessData;
            appendKlongs(parent, depth - 1, pd.oneKwi, pd);

            pd.splitListener.nodeSplit(Dag.SPACE_SPLIT_2);
            assert parent.checkWithMessage() == null : parent.checkWithMessage() + " node:\n"
                    + parent.print();
            assert newSegmentRoot.checkWithMessage() == null;
            
        } else {
            //
            // space-split-1:
            // 'node' is not a segment root since parent is not a segment leaf.
            //
            
            long secondKlong = node.firstAndSecond(tt, last, toInsert, first, second);
            reportNewPointers(first, pd.pointerCreatedListener);
            reportNewPointers(second, pd.pointerCreatedListener);
            pd.nodeChangeListener.keyNodeChanged(first);
            pd.nodeChangeListener.keyNodeChanged(second);
            
            long firstKlong = pd.keyAccessPath.getKlong(depth);

            pd.twoKwis[0].klong = firstKlong;
            pd.twoKwis[0].node = first;
            pd.twoKwis[0].pos = pd.accessData;
            pd.twoKwis[1].klong = secondKlong;
            pd.twoKwis[1].node = second;
            pd.twoKwis[1].pos = pd.accessData;

            appendKlongs(parent, depth - 1, pd.twoKwis, pd);

            pd.splitListener.nodeSplit(Dag.SPACE_SPLIT_1);
            assert parent.checkWithMessage() == null : parent.checkWithMessage();
        }
    }

    private void reportNewPointers(KeyNode node, PointerCreatedListener listener) {
        int size = node.size;
        for (int i = 0; i < size; i++) {
            Node pointee = node.getPointerNode(i);
            if (pointee != null) {
                listener.pointerCreated(node, i, pointee);
            }
        }
    }
    
    
    // ======== Inner types ========
    
    /**
     * A NodeReader has method readNode() that can read a node from the DB stream
     * give the spos of the node.
     */
    public static interface NodeReader {
        
        /**
         * Reader a node from the stream. Assumes the item exists at the location 
         * and that it is valid.
         * 
         * @throws StreamFormatException
         * @throws StreamIoException
         */
        public Node readNode(long spos);
    }
    
    /**
     * A PointerListener is used to listen to pointer-followed events
     * and super-root-node-accessed events.
     */
    public static interface PointerListener {
        /**
         * Called from TopDs findRoot() to report that the super root node was
         * accessed.
         */
        public void superRootAccessed(TopNode superRoot);
        
        /**
         * Reports that a pointer was followed.
         * 
         * @param pointerType One of Pointer.TYPE_MEMORY, Pointer.TYPE_STREAM.
         */
        public void pointerFollowed(
                Node predecessor, int pointerIndex, Node result, int pointerType);
    }
    
    public static final PointerListener DO_NOTHING_POINTER_LISTENER = new PointerListener() {
        public void pointerFollowed(Node predecessor, int pointerIndex, Node result,
                int pointerType) {}

        public void superRootAccessed(TopNode mySuperRoot) {}
    };
    
    
    public static interface PointerCreatedListener {
        /**
         * Reports that a node from 'from' to 'to' was created.
         * Report this AFTER 'from' and 'to' have been created and the node creation
         * has been reported to the NodeChangeListener.
         * 
         * @param index  Pointer index of pointer created.
         */
        public void pointerCreated(Node from, int index, Node to);
    }
    
    public static final PointerCreatedListener DO_NOTHING_POINTER_CREATED_LISTENER = 
        new PointerCreatedListener() {
            public void pointerCreated(Node from, int index, Node to) {}
        };
    
    
    /**
     * The cache policy determines whether to cache nodes read from stream.
     * This interface enables us to easily set a cache policy such as:
     * cache all nodes read from stream, cache no nodes, cache only KeyNodes, cache all
     * KeyNodes and all ValueNodes that are smaller than 400k in size.
     * Cache policy can be set per get operation.
     */
    public static interface CachePolicy {
        /**
         * If true is returned, the node will be cached.
         * 
         * @param node  A node that was just read from the stream.
         * @return True to cache the node.
         */
        public boolean shouldCache(Node node);
    }
    
    public static final CachePolicy CACHE_ALL = new CachePolicy() {
        public boolean shouldCache(Node node) {
            return true;
        }
    };
    
    public static final CachePolicy CACHE_NOTHING = new CachePolicy() {
        public boolean shouldCache(Node node) {
            return false;
        }
    };
    
    /**
     * Cache policy that caches all nodes except for ValueNodes with a value larger 
     * than 1 MiB.
     */
    public static final CachePolicy CACHE_ALL_EXCEPT_LARGE_VALUE_NODES = new CachePolicy() {
        public boolean shouldCache(Node node) {
            boolean result;
            int type = node.getType();
            if (type == Node.TYPE_VALUE) {
                result = ((ValueNode) node).getValue().length <= 1024*1024;
            } else {
                result = true;
            }
            return result;
        }
    };
    
    /**
     * Listens to Db graph nodes that are created or changed.
     */
    public static interface NodeChangeListener {
        
        /**
         * Reports that a TopNode was created.
         */
        public void topNodeCreated(TopNode node);
        
        /**
         * Reports that a new KeyNode was created.
         */
        public void keyNodeCreated(KeyNode node);
        
        /**
         * Reports that a ValueNode was created.
         */
        public void valueNodeCreated(ValueNode node, long[] key);
        
        /**
         * Reports that an existing KeyNode was appended to.
         */
        public void keyNodeChanged(KeyNode node);
        
        /**
         * Reports that a KeyNode that existed before the current transaction was replaced by
         * a split, or unlinked by a delete (bergdb 023-05, P1): it is no longer current, and it
         * has no klongs of the transaction (Dag.handleFullNode, Dag.unlink). Added 2026-10-16;
         * does nothing by default.
         */
        public default void keyNodeReplaced(KeyNode node) {}
        
        /**
         * Reports that a KeyNode that the current transaction made was taken back (bergdb
         * 023-05, P4, as P2's keyNodeDropped: Dag.takeBack, Dag.takeBackRoot): no node names
         * it, and it is never written. As keyNodeReplaced, and its object leaves the node
         * table. Calls keyNodeReplaced by default.
         */
        public default void keyNodeTakenBack(KeyNode node) {
            keyNodeReplaced(node);
        }
        
        /**
         * Reports that the super root, which existed before the current transaction, was
         * replaced by a new super root (TopDs.newSuperRoot). Added 2026-10-16; does nothing
         * by default.
         */
        public default void topNodeReplaced(TopNode node) {}
    }
    
    public static final NodeChangeListener DO_NOTHING_NODE_CHANGE_LISTENER = new NodeChangeListener() {
        public void topNodeCreated(TopNode node) {}
        public void keyNodeCreated(KeyNode node) {}
        public void keyNodeChanged(KeyNode node) {}
        public void valueNodeCreated(ValueNode node, long[] key) {}
    };
    
    
    
    public static final int TIME_SPLIT_1 = 1;
    public static final int TIME_SPLIT_2 = 2;
    public static final int SPACE_SPLIT_1 = 11;
    public static final int SPACE_SPLIT_2 = 12;
    public static final int SPACE_SPLIT_3 = 13;
    
    /**
     * Used to listen to node split events.
     */
    public static interface SplitListener {
        public void nodeSplit(int splitType);
    }
    
    public static final SplitListener DO_NOTHING_SPLIT_LISTENER = new SplitListener() {
        public void nodeSplit(int splitType) {}
    };
}
