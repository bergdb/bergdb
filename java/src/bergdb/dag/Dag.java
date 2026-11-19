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
    private final TopDs topDs;
    private final int maxNodeSize;
    
    /**
     * The largest node size, 62 (Frans, 2026-11-12; bergdb 024-19, Q6): a delete bitmap is one
     * klong of 62 bits, one for each klong index of its node (Klong.DELETE_BITS; bergdb 027-03,
     * section 11.2). DbBuilder offers 8, 14, 30 (the default and the Pub API's) and 62; a Dag
     * refuses a larger size when it is made (checkNodeSize).
     */
    public static final int MAX_NODE_SIZE = 62;
    
    /** @throws IllegalArgumentException  If maxNodeSize is above MAX_NODE_SIZE, 62. */
    public Dag(TopNode superRoot, int maxNodeSize) {
        checkNodeSize(maxNodeSize);
        this.topDs = new TopDs(superRoot);
        this.maxNodeSize = maxNodeSize;
    }
    
    /**
     * Refuses a node size above MAX_NODE_SIZE (bergdb 024-19, Q6). Until 2026-11-12 a Dag took
     * any size, and one above 62 failed at its first delete bit beyond 61 (024-19, 2.2).
     */
    private static void checkNodeSize(int maxNodeSize) {
        if (maxNodeSize > MAX_NODE_SIZE) {
            throw new IllegalArgumentException("The node size " + maxNodeSize + " is above "
                    + MAX_NODE_SIZE + ", the largest: a delete bitmap names " + MAX_NODE_SIZE
                    + " klongs of its node (bergdb 024-19, Q6).");
        }
    }
    
    /**
     * Factory method to create minimal Dag with two nodes: a top node and a key node.
     * The database is empty; no KVs.
     * 
     * @throws IllegalArgumentException  If maxNodeSize is above MAX_NODE_SIZE, 62.
     */
    public static Dag createEmpty(long time, int maxNodeSize, PointerFollower pointerFollower, 
            Dag.PointerCreatedListener pointerCreationListener) {
        checkNodeSize(maxNodeSize);
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
        return new PutData();
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
    

    // ======== The writer: putKvs() (bergdb 026-25) ========
    //
    // Since record format 8 the writer is PE, "plan, then emit" (PeWriter; bergdb 026-23,
    // section 1.2; 026-24; the proof 030-21): a transaction's operations change the tree as one
    // batch, each node decided once from the whole batch and written once. It replaced the
    // writer of record formats 2 to 7, which applied a transaction's operations one by one,
    // each with its splits, time splits, space splits in place, the upward unlink of a delete,
    // LE-b's relabel, the merges at the delete, root collapse and the take-back of a node that
    // the transaction made and emptied (release 2026.5's Dag.java, putKv() and below).
    //

    /**
     * Counts of the writer's decisions, for tests and measurements; written by the writer only
     * (PeWriter): transactions; nodes that got klongs appended; nodes replaced by one new node,
     * by their size or (compactions) by their dead klongs, or cut into two or more; joins of
     * two children (the merges); root collapses; new roots above a root cut; planned nodes
     * dropped empty.
     */
    public static volatile long statTransactions, statAppends, statReplaces, statCompactions,
            statCuts, statJoins, statCollapses, statNewRoots, statDropped;
    
    /**
     * <p>Applies a transaction's operations to the graph at the time pd.tt: for each i, a put
     * of keys[i] with values[i], or a delete if values[i] is null. The keys are strictly
     * increasing (Keys.compareArrays): one operation a key, in key order, as Db.putKvs gives
     * them, and the start's rerun a record's KVs. A delete of a key with no value is a noop:
     * it makes nothing, and its key is not stored.</p>
     *
     * <p>This method runs with exclusive write access to the data structure (synchronized on
     * Db.writeLock). However, there may be concurrent readers that read with a lookup time
     * strictly less than the transaction time.</p>
     *
     * <p>Out: the changes to the graph; the nodes made, changed, replaced and on the path of a
     * change reported to pd.nodeChangeListener (with the values and the delete nodes made, in
     * key order, and the top node made last), the pointers made to pd.pointerCreatedListener.
     * ALL modifications to the Dag are done through this method (PeWriter).</p>
     *
     * @throws DbException
     */
    public void putKvs(long[][] keys, byte[][] values, PutData pd) {
        assert pd.tt >= 0;
        assert pd.nodeChangeListener != null;
        assert pd.pointerListener != null;
        assert pd.pointerCreatedListener != null;
        if (keys.length != values.length) {
            throw new IllegalArgumentException(keys.length + " keys, " + values.length
                    + " values");
        }
        for (int i = 0; i < keys.length; i++) {
            if (keys[i] == null || keys[i].length == 0) {
                throw new IllegalArgumentException("key " + i + " is null or has no segment");
            }
            if (i > 0 && Keys.compareArrays(keys[i - 1], keys[i]) >= 0) {
                throw new IllegalArgumentException("the keys are not strictly increasing at " + i
                        + " (one operation a key, in key order)");
            }
        }
        if (keys.length == 0) {
            return;                 // no operation: nothing changes
        }
        new PeWriter(this, keys, values, pd).run();
    }

    /**
     * A transaction of one operation at pd.tt (putKvs()): a put of 'key' with 'value', or a
     * delete if 'value' is null. A transaction's operations go to the writer as one batch, so a
     * second call at the same time is another transaction, which the writer does not allow:
     * for tests that make a transaction of one operation.
     */
    public void putKv(long[] key, byte[] value, PutData pd) {
        putKvs(new long[][] {key}, new byte[][] {value}, pd);
    }

    /** The node size, the most klongs of a key node. */
    public int getMaxNodeSize() {
        return maxNodeSize;
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
     * The cut size for node size 'b': the most entries of each of the new nodes that the
     * writer cuts a list into when it does not fit one node (PeWriter's cutParts; Contract.PE's
     * cap): b / 2, 15 at node size 30 (bergdb 026-24, section 2.6: with the cut size h, 17, the
     * trial's trees were fuller and index updates wrote 1 to 2 percent more than the writer of
     * format 7; with b / 2 less on every trace of its two sets). A rule of record format 8, as
     * the thresholds are; the Lean model's Pe.cutSize.
     */
    public static int cutSize(int b) {
        return b / 2;
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

    /** The least theta from node size 8 (Frans, 2026-11-12; bergdb 024-19, Q4). */
    static final int THETA_MIN = 2;

    /**
     * theta for node size 'b': THETA_30 * b / 30 by integer division, at least 2, from node size
     * 8 (2 at 8, 3 at 14, 14 at 62); 0, off, below it, where format 7 merges nothing either
     * (bergdb 024-23, OD2; other node sizes are open with 024-14's QT2). A rule of record
     * format 7, as the thresholds are. The floor was 1 until 2026-11-12 (Frans, 024-19, Q4):
     * theta 1 at 8 compacted a node at every second dead klong and cost 25 percent of the
     * bytes a put (024-19, section 4.5).
     */
    public static int theta(int b) {
        return b < MERGE_MIN_NODE_SIZE ? 0
                : Math.max(THETA_MIN, THETA_30 * b / THRESHOLDS_NODE_SIZE);
    }

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
         * Reports that a KeyNode that existed before the current transaction is no longer
         * current: replaced by new nodes, joined with a sibling, emptied, or collapsed (since
         * record format 8, PeWriter; until then replaced by a split, or unlinked by a delete,
         * bergdb 023-05, P1). It has no klongs of the transaction. Added 2026-10-16; does
         * nothing by default.
         */
        public default void keyNodeReplaced(KeyNode node) {}
        
        /**
         * Reports that a KeyNode that the transaction keeps as it was is on the path of its
         * change: a node below it was made or got klongs (PeWriter, bergdb 026-25), so that Db
         * makes it dirty, as the Lean model's step 3 marks a node with a changed node below it
         * (SIS/Algorithm.lean, marked). A node made or changed is on the path too, and its
         * keyNodeCreated or keyNodeChanged says so. Does nothing by default.
         */
        public default void keyNodeOnPath(KeyNode node) {}
        
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
}
