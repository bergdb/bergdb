package bergdb.core;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import bergdb.dag.Pointee;
import bergdb.dag.Handle;
import bergdb.dag.Klong;
import bergdb.dag.KeyNode;
import bergdb.dag.KlongWithPointer;
import bergdb.dag.Node;
import bergdb.dag.Pointer;
import bergdb.dag.Spos;
import bergdb.dag.TopNode;

/**
 * The audit (bergdb item 001, WP J1; test-only): the invariants of the Lean model's
 * physical layer (bergdb 001-08, 5.3; lean/SIS/Evict.lean until bergdb 005-62) checked on
 * Java's own state at a transaction boundary, for stress programs that ask for it (the
 * system property audit=N: every N-th transaction; 0, the default, off). It reads the stream but
 * changes nothing: no slot, no node table entry, no dirty flag.
 *
 * <ol>
 * <li><b>The resident objects</b> (Residents.walk): every object reachable through memory
 * slots from the super root, the node table and D.</li>
 * <li><b>INV-CAN</b>: one canonical object per node id among them, the node table's; and a
 * clean canonical object is its node's latest version (WP J3: a node released and loaded
 * again is made canonical from that version only), when the oracle knows the node.</li>
 * <li><b>Handles</b> (bergdb item 009, steps 3a and 3d): the node table's handles are live,
 * each with an object of its node or none; a live handle that a pointer of a resident object
 * holds is the table's (one live handle per node id); a dead handle has no object. Until
 * step 3a the node table named canonical objects only (bergdb item 001, WP R8, change 3);
 * with handles, a handle may hold a version read.</li>
 * <li><b>Pins</b>: every object of D (TransSeq) is resident, canonical, dirty and the node
 * table's; the super root is canonical and the table's; the record being written is empty
 * between transactions; and every dirty resident index object is in D.</li>
 * <li><b>INV-SLOT</b> (5.4): every slot of a resident canonical index object of a node that
 * is current (reachable at the latest time) or in D names, unless its pointee is pinned,
 * the pointee's latest version: a memory slot its object's position, a stream slot its
 * position after Rule R. The latest versions come from an oracle that Db keeps in this
 * mode from the records it appends, and from the startup section (Rule R's map, and the
 * values the rerun meets): a pointee written before the startup section of the last
 * startup is not known to it and not checked. A slot below the stream's first position
 * (a dead pointer after a cut, M33) is not checked.</li>
 * <li><b>No dangling slot</b>: the walk reaches every object a resident slot names, by
 * construction; a memory slot to a released object (J3) would be one.</li>
 * </ol>
 *
 * Returns the failures, at most 20, each a line of text; empty if none.
 */
public final class Audit {
    /** Audit every N-th transaction (the property audit); 0: off. */
    public static final int EVERY = Integer.getInteger("audit", 0);

    private static final int MAX_FAILURES = 20;

    private static long audits = 0;
    private static long failed = 0;
    private static String first = null;
    private static long residentSeen = 0;      // resident objects, summed over the audits
    private static long slotsChecked = 0;      // INV-SLOT: slots compared with the oracle
    private static long slotsPinned = 0;       // INV-SLOT: slots whose pointee is pinned
    private static long slotsUnknown = 0;      // INV-SLOT: pointees the oracle does not know
    private static long lastEstimate = 0;      // accounting: Residents.bytes() at the last audit
    private static long lastWalked = 0;        // accounting: the walked objects' bytes then

    private Audit() {}

    /**
     * Records the result of an audit (when: "startup" or "transaction"): counted, and the first
     * failing audit's failures kept and printed to System.err.
     */
    static synchronized void record(List<String> failures, String when) {
        audits++;
        if (failures.isEmpty()) return;
        failed++;
        if (first == null) {
            StringBuilder b = new StringBuilder("audit after " + when + ":");
            for (String f : failures) b.append("\n  ").append(f);
            first = b.toString();
            System.err.println("AUDIT FAILED " + first);
        }
    }

    /** The number of audits that failed so far, in this process. */
    public static synchronized long failures() {
        return failed;
    }

    /**
     * One line for a stress program's output: "AUDIT: n audits, f failed", or "AUDIT: off".
     */
    public static synchronized String summary() {
        if (EVERY <= 0) return "AUDIT: off";
        return "AUDIT: " + audits + " audits (every " + EVERY + " transactions and at every startup), "
                + failed + " failed; " + residentSeen + " resident objects, INV-SLOT " + slotsChecked
                + " slots checked, " + slotsPinned + " to pinned nodes, " + slotsUnknown
                + " to nodes the oracle does not know; accounting at the last audit: estimate "
                + lastEstimate + " bytes, the resident objects " + lastWalked + " bytes"
                + (first == null ? "" : "; first: " + first.replace('\n', ' '));
    }

    /**
     * The latest written position of each node, by id: the audit's oracle for INV-SLOT,
     * kept by Db when the audit is on (EVERY > 0). Positions only grow: a node's latest
     * version is the last one appended.
     */
    public static final class Oracle {
        private final HashMap<Long, Long> latest = new HashMap<Long, Long>();

        /** The record just appended: its nodes' positions (set by NodeStream.appendNodes). */
        synchronized void appended(TransNodes tn) {
            for (int i = 0; i < tn.topCount; i++) put(tn.topNodes[i]);
            for (int i = 0; i < tn.keyCount; i++) put(tn.keyNodes[i]);
            for (int i = 0; i < tn.valueCount; i++) put(tn.valueNodes[i]);
        }

        /** Startup: the newest position in the startup section of each index node in it. */
        synchronized void section(Map<Long, Long> newById) {
            for (Map.Entry<Long, Long> e : newById.entrySet()) {
                Long old = latest.get(e.getKey());
                if (old == null || old < e.getValue()) latest.put(e.getKey(), e.getValue());
            }
        }

        /** Startup: a value node of the startup section, which the rerun recreates. */
        synchronized void value(long id, long pos) {
            if (Spos.isValid(pos) && !Spos.isVpos(pos)) latest.put(id, pos);
        }

        private void put(Node n) {
            long pos = n.getSpos();
            if (Spos.isValid(pos) && !Spos.isVpos(pos)) latest.put(n.getId(), pos);
        }

        /** The latest position of node id, or null if not known. */
        synchronized Long latest(long id) {
            return latest.get(id);
        }
    }

    /**
     * Audits db. The caller holds db's write lock, between transactions (no transaction
     * executing).
     */
    public static List<String> check(Db db) {
        final List<String> failures = new ArrayList<String>();
        final Db.Internal in = db.internal();
        final Cache3 table = in.cache();
        final Oracle oracle = in.oracle();
        final TopNode superRoot = in.superRoot();
        final NodeStream ns = in.nodeStream();
        final NodeCollection nc = in.nodeCollection();

        // D's objects.
        final List<Node> dObjects = new ArrayList<Node>();
        final Set<Node> dSet = Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());
        in.transSeq().visitGotDirtyNodes(Long.MAX_VALUE, new TransSeq.NodeVisitor() {
            public void node(Node node, long tpos, long lastTpos) {
                dObjects.add(node);
                dSet.add(node);
            }
        });

        // 1. The resident objects.
        final List<Node> tableObjects = table.nodes();
        final List<Node> resident = Residents.walk(superRoot, tableObjects, dObjects);
        long checked = 0, pinned = 0, unknown = 0;

        // 2. INV-CAN.
        HashMap<Long, Node> canonicalById = new HashMap<Long, Node>();
        for (Node n : resident) {
            if (!n.isIndexNode() || !n.isCanonical()) continue;
            Node other = canonicalById.put(n.getId(), n);
            if (other != null && other != n) {
                fail(failures, "INV-CAN: two canonical objects for node " + n.getId());
            }
            if (table.getNode(n.getId()) != n) {
                fail(failures, "INV-CAN: canonical object of node " + n.getId()
                        + " is not the node table's");
            }
            Long latest = oracle == null || n.isDirty() ? null : oracle.latest(n.getId());
            if (latest != null && n.getSpos() != latest) {
                fail(failures, "INV-CAN: the clean canonical object of node " + n.getId()
                        + " is the version at " + n.getSpos() + ", its latest is at " + latest);
            }
        }
        // The handles (bergdb item 009, step 3a): the table's are live, each with its node's
        // object or none; a handle's object is of its node. A handle may hold a version that
        // is not canonical (until step 3a the node table named canonical objects only).
        for (Handle h : table.handles()) {
            if (h.isDead()) {
                fail(failures, "handles: the node table has a dead handle of node " + h.id);
            }
            Node o = h.obj;
            if (o != null && o.getId() != h.id) {
                fail(failures, "handles: the handle of node " + h.id + " holds an object of node "
                        + o.getId());
            }
        }

        // 3. Pins.
        for (Node n : dObjects) {
            if (!n.isCanonical() || !n.isDirty() || table.getNode(n.getId()) != n) {
                fail(failures, "pins: object of D for node " + n.getId() + " is not the canonical, "
                        + "dirty object of the node table (canonical " + n.isCanonical() + ", dirty "
                        + n.isDirty() + ")");
            }
        }
        if (superRoot == null || !superRoot.isCanonical() || table.getNode(superRoot.getId()) != superRoot) {
            fail(failures, "pins: the super root is not canonical or not the node table's");
        }
        if (in.x().transNodes.size() != 0) {
            fail(failures, "pins: the record being written is not empty between transactions");
        }
        for (Node n : resident) {
            if (n.isIndexNode() && n.isDirty() && !dSet.contains(n)) {
                fail(failures, "pins: dirty object of node " + n.getId() + " is not in D");
            }
            if (n.isIndexNode() && n.isInTransNodes()) {
                fail(failures, "pins: object of node " + n.getId() + " is in TransNodes between "
                        + "transactions");
            }
        }

        // The handles in the pointers (bergdb item 009, step 3d): a live handle that a pointer
        // of a resident object holds is the table's handle for its node (one live handle per
        // node id, 009-02, 4.10); a dead one has no object.
        for (Node x : resident) {
            if (!x.isIndexNode()) continue;
            int size = x.getSize();
            for (int i = 0; i < size; i++) {
                Pointee pe = x.getPointee(i);
                if (!(pe instanceof Handle)) continue;
                Handle h = (Handle) pe;
                if (h.isDead()) {
                    if (h.obj != null) {
                        fail(failures, "handles: a dead handle of node " + h.id + " has an object");
                    }
                } else if (h.state() == Handle.LIVE && table.liveHandle(h.id) != h) {
                    fail(failures, "handles: pointer " + i + " of node " + x.getId()
                            + " holds a live handle of node " + h.id + " that is not the table's");
                }
            }
        }

        // 4. INV-SLOT, for the canonical objects of current nodes and of D.
        final long time = db.lookupTime(Long.MAX_VALUE);
        final Set<Long> current = currentIds(db, time, oracle);
        final long firstPos = ns.getFirstPos();
        for (Node n : resident) {
            if (!n.isIndexNode() || !n.isCanonical()) continue;
            if (!current.contains(n.getId()) && !dSet.contains(n)) continue;
            int size = n.getSize();
            for (int i = 0; i < size; i++) {
                Node c = n.getPointerNode(i);
                long pos = c == null ? n.getSerializedRef(i) : n.getPointerPos(i);
                if (Pointer.isNull(c, pos)) continue;
                if (c == null && !Spos.isVpos(pos) && pos < firstPos) continue;      // M33
                Pointee pe = n.getPointee(i);
                long id = c != null ? c.getId() : pe instanceof Handle ? ((Handle) pe).id
                        : (Spos.isVpos(pos) ? pos : ns.readNodeHeader(pos).id());
                Node canon = table.getNode(id);
                if (canon != null && Residents.isPinned(canon, superRoot)) {
                    pinned++;
                    continue;
                }
                // The reference a record would get now (the record rule, 009-02, 4.6), and
                // Rule R, which the writer applies before it writes, unless a canonical
                // object decides it.
                long ref = n.getSerializedRef(i);
                if (c == null || !c.isCanonical()) {
                    Long newPos = nc.newestInSection(id);
                    if (newPos != null && Spos.newer(newPos, ref)) ref = newPos;
                }
                Long expected = oracle == null ? null : oracle.latest(id);
                if (expected == null) {
                    unknown++;
                    continue;
                }
                checked++;
                if (ref != expected) {
                    fail(failures, "INV-SLOT: node " + n.getId() + ", slot " + i + " for node " + id
                            + " names " + ref + ", its latest version is at " + expected
                            + (c != null ? (c.isCanonical() ? " (memory, canonical)" : " (memory, snapshot)")
                            : " (stream)"));
                }
            }
        }
        long walked = 0;
        for (Node n : resident) walked += n.getMemSize();
        synchronized (Audit.class) {
            lastEstimate = table.residents().bytes();
            lastWalked = walked;
            residentSeen += resident.size();
            slotsChecked += checked;
            slotsPinned += pinned;
            slotsUnknown += unknown;
        }
        return failures;
    }

    private static void fail(List<String> failures, String s) {
        if (failures.size() < MAX_FAILURES) failures.add(s);
    }

    /**
     * The ids of the nodes reachable at 'time' (the current nodes), through live pointers
     * from the super root. A node is read from its canonical object if it has one, else
     * from the object a memory slot names, else from the stream: the latest version the
     * oracle knows, or the slot's position after Rule R. Nothing is cached.
     */
    static Set<Long> currentIds(Db db, long time, Oracle oracle) {
        final Db.Internal in = db.internal();
        final Cache3 table = in.cache();
        final NodeStream ns = in.nodeStream();
        final NodeCollection nc = in.nodeCollection();
        Set<Long> ids = new HashSet<Long>();
        ArrayDeque<Node> todo = new ArrayDeque<Node>();
        TopNode superRoot = in.superRoot();
        todo.add(superRoot);
        KlongWithPointer kwi = new KlongWithPointer();
        while (!todo.isEmpty()) {
            Node x = todo.poll();
            if (!ids.add(x.getId())) continue;
            if (x instanceof TopNode) {
                TopNode t = (TopNode) x;
                Node r = load(t.getPointerNode(0), t.rootPointerPos, table, ns, nc, oracle);
                if (r != null) todo.add(r);
            } else if (x instanceof KeyNode) {
                KeyNode k = (KeyNode) x;
                int size = k.size;
                HashSet<Long> cvs = new HashSet<Long>();
                for (int i = 0; i < size; i++) {
                    if (Klong.getIntType(k.klongs[i]) == Klong.INT_TYPE_KEY) {
                        cvs.add(Klong.getCompareValue(k.klongs[i]));
                    }
                }
                for (long cv : cvs) {
                    k.searchEq(time, cv, kwi);
                    if (kwi.klong == Klong.NULL || kwi.isNullPointer()) continue;
                    Node c = load(kwi.node, kwi.pos, table, ns, nc, oracle);
                    if (c != null && c.isIndexNode()) todo.add(c);
                    else if (c != null) ids.add(c.getId());
                }
            }
        }
        return ids;
    }

    private static Node load(Node mem, long pos, Cache3 table, NodeStream ns, NodeCollection nc,
            Oracle oracle) {
        long id;
        if (mem != null) {
            id = mem.getId();
        } else if (pos == Spos.NULL) {
            return null;
        } else if (Spos.isVpos(pos)) {
            id = pos;
        } else if (pos < ns.getFirstPos()) {
            return null;
        } else {
            id = ns.readNodeHeader(pos).id();
        }
        Node canon = table.getNode(id);
        if (canon != null && canon.isCanonical()) return canon;
        if (mem != null) return mem;
        Long latest = oracle == null ? null : oracle.latest(id);
        long ref = latest != null ? latest : pos;
        if (latest == null) {
            Long newPos = nc.newestInSection(id);
            if (newPos != null && Spos.newer(newPos, ref)) ref = newPos;
        }
        if (Spos.isVpos(ref)) return null;
        return ns.readNode(ref);
    }
}
