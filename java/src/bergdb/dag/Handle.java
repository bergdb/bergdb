package bergdb.dag;

import java.lang.invoke.MethodHandles;
import java.lang.invoke.VarHandle;

/**
 * A handle (bergdb item 009; items/009-handles/02-implementation-plan.md, 4.1): one per index
 * node that has a resident object or that a pointer of a resident object names. A memory
 * pointer of a key node or a top node holds its pointee's handle, and the handle holds the
 * node's one object, canonical or a version, so that evicting the object changes the handle
 * only: nothing needs to know which pointers name the node.
 *
 * <p>States: LIVE, the node table's handle for the node (Cache3), with an object or not;
 * LOADING, a loader holds the handle's monitor and reads a version from the stream (009-02,
 * T7a); DEAD, evicted: out of the table, no object, never live again. A pointer that holds a
 * dead handle finds the node's live handle again by the id (T3a).</p>
 *
 * <p>Concurrency (009-02, 3.3 and 3.4): the id is final, so a thread that sees a handle
 * through a race sees its id; obj is volatile, written by an install or an eviction, and the
 * fast path reads it with that edge; the state changes only by compareAndSet, and LIVE is 0,
 * the default, so a new handle is live without a write in its constructor; writtenPos is
 * written only by an eviction (Cache3.kill), before the object leaves the handle, and read
 * by the record rule and by the slow path, which sees it through obj (a reader that follows
 * the pointer at a time after the node's write sees the install, and then the eviction's
 * null; one that does not, reads a version that is right for its own time); the CLOCK bit
 * is a hint, read and written plainly.</p>
 */
public final class Handle implements Pointee {
    /** The states. LIVE is 0, the default value of a byte field. */
    public static final byte LIVE = 0, LOADING = 1, DEAD = 2;

    /** The node id. */
    public final long id;

    /** The node's one object: canonical, or the newest version loaded; or null. */
    public volatile Node obj;

    /**
     * Where the node's canonical object was when an eviction killed this handle, Spos.NULL if
     * none: set only by that eviction (Cache3.kill; live handles have none, as the model's
     * HLiveWrittenOK says), under the map's lock and the write lock; read by the record rule
     * (serializedRef; 009-02, 4.6) and by the slow path, which raises a pointer's reference
     * to it (NodeCollection.followStreamPointer).
     */
    public long writtenPos = Spos.NULL;

    /** LIVE, LOADING or DEAD; changed only by casState. */
    private volatile byte state;

    /** The CLOCK bit (009-02, 4.7): set by a follow when clear, cleared by eviction. */
    public byte ref;

    private static final VarHandle STATE;
    static {
        try {
            STATE = MethodHandles.lookup().findVarHandle(Handle.class, "state", byte.class);
        } catch (ReflectiveOperationException e) {
            throw new ExceptionInInitializerError(e);
        }
    }

    public Handle(long id) {
        this.id = id;
    }

    public Handle(long id, Node obj) {
        this.id = id;
        this.obj = obj;
    }

    /**
     * True if object o may serve a pointer whose reference is ref (009-02, 4.4): a canonical
     * object serves every lookup time; a version at ref or later serves every time the
     * version at ref serves (lemma M of the Lean model). A vpos names no stream position,
     * so a pointer that holds one is served by a canonical object only.
     */
    public static boolean usable(Node o, long ref) {
        return o.isCanonical() || (!Spos.isVpos(ref) && o.getSpos() >= ref);
    }

    /**
     * What a pointer to node object n holds: n itself if it is a value, else n's handle, the
     * back reference set when the object was put into a handle (KeyNode.handle,
     * TopNode.handle); null for null. An index node object that was never put into a
     * handle (a test's node, the primordial transaction's) gets one here, outside any node
     * table.
     */
    public static Pointee pointeeOf(Node n) {
        if (n == null) return null;
        if (n instanceof ValueNode) return (ValueNode) n;
        return of(n);
    }

    /** The handle of index node object n: its back reference, made if it has none. */
    public static Handle of(Node n) {
        if (n instanceof KeyNode) {
            KeyNode k = (KeyNode) n;
            if (k.handle == null) k.handle = new Handle(k.getId(), k);
            return k.handle;
        }
        if (n instanceof TopNode) {
            TopNode t = (TopNode) n;
            if (t.handle == null) t.handle = new Handle(t.getId(), t);
            return t.handle;
        }
        throw new IllegalArgumentException("not an index node: " + n);
    }

    /**
     * The record rule of 009-02, 4.6, for a pointer that holds p and has reference ref: a
     * value's position; the canonical object's position if p is a handle that holds a
     * canonical object; else the newer of ref (after Rule R, which the writer applies first)
     * and the position this process last wrote the node at (writtenPos).
     */
    public static long serializedRef(Pointee p, long ref) {
        if (p instanceof ValueNode) return ((ValueNode) p).getSpos();
        if (p instanceof Handle) {
            Handle h = (Handle) p;
            Node o = h.obj;
            if (o != null && o.isCanonical()) return o.getSpos();
            long w = h.writtenPos;
            if (Spos.isValid(w) && !Spos.isVpos(w) && (Spos.isVpos(ref) || w > ref)) return w;
        }
        return ref;
    }

    public byte state() {
        return state;
    }

    public boolean isDead() {
        return state == DEAD;
    }

    /** Changes the state from 'from' to 'to' if it is 'from'; true if it did. */
    public boolean casState(byte from, byte to) {
        return STATE.compareAndSet(this, from, to);
    }

    public String toString() {
        String s = state == LIVE ? "live" : state == LOADING ? "loading" : "dead";
        Node o = obj;
        return "handle(" + id + ", " + s + ", " + (o == null ? "no object" : "spos " + o.getSpos()
                + (o.isIndexNode() && o.isDirty() ? ", dirty" : "")) + ")";
    }
}
