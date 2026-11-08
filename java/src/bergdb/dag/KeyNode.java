package bergdb.dag;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.lang.invoke.VarHandle;

import bergdb.common.StringUtil;
import bergdb.nanotest.Assert;

/**
 * <p>A key node has an array of "klongs" and corresponding Node references.</p>
 * 
 * <p>Conceptually, we define "write access". An object of this class allows multiple concurrent
 * readers all the time; also when a writer has access to the object.
 * However, only a single thread at a time can have write access to this object.
 * This must be enforced externally. Methods that require "write access" from the caller 
 * are documented with "Write access required".</p>
 * 
 * <p>For developers: The concurrency properties of the class is based on the volatile field 
 * KeyNode.size. Is is also based on the fact that the used size of arrays (klongs, pointers, pos) 
 * only grows. 
 * Existing data in them does not change. Therefore the writer can safely write to the previously 
 * unused area at the end of the arrays (range: size..array.length-1) while readers concurrently 
 * read the range 0..size-1 of the arrays. Once KeyNode.size is increased by the writer, all writes 
 * are visible for the readers as they read the KeyNode.size field.</p>
 *
 * <p>A growth (growCapacity, setContentFrom) replaces the three arrays by copies, and a reader
 * that read size before it may read the new arrays. The three fields are volatile (bergdb
 * 015-14; in 015-12 a release fence before plain stores): a growth stores them after its
 * copies, and a reader reads each with a volatile read, so it sees the copies of every array
 * it reads (JLS 17.4.4 and 17.4.5), whichever size it read. Only the writer stores them.</p>
 * 
 * <p>Two exceptions, both for klongs of the current transaction, which no reader sees: readers
 * use lookup times before the transaction time, and every read stops at the first time klong
 * after its lookup time (2026-10-16, Dag.handleFullNode):</p>
 * <ul>
 * <li>A node that existed before the transaction and that the transaction replaces by a split
 * loses its klongs of the transaction: its size goes down (toPreviousState). A reader that read
 * the larger size stops at the time klong of the transaction, before the slots that are now
 * unused. The writer never adds klongs to the node again: it is not current.</li>
 * <li>A node with no klongs before the transaction (the transaction created it, or it was
 * empty) gets new arrays in place when it is split (setContentFrom). Its first klong, before
 * and after, is the time klong of the transaction, where every reader stops.</li>
 * </ul>
 *
 * <p>Pointers change in place (bergdb item 009; items/009-handles/02-implementation-plan.md,
 * 3.3 and 3.4): what pointer i holds (pointers[i]: nothing, a handle of its node, live or
 * dead, or its value) and its reference (pos[i], raised by Rule R or by a reader's slow
 * path). What it names, the node or the value, never changes (C1). Every such change is made
 * under the node's monitor (C2); a change of what a pointer holds is a release store
 * (setPointee, setPointer, swizzle), and a change of a reference an opaque store (setRef,
 * raiseRef, setPointer). A reader reads pointers[i] without a lock with an acquire
 * (getPointee), for a handle as for a value, and then pos[i] with an opaque read
 * (getPointerPos). The acquire pairs with the release store that put the pointee there, so
 * the reader sees what came before that store: for a handle, the raise of the reference and
 * the install of the handle's object; for a value, its fields (C5). Opaque, as a reader may
 * read pos[i] in a race and a plain long may tear (JLS 17.7). Before bergdb 015-14, a pointer
 * to a handle and pos[i] were read plainly, which rested on the address dependency and on a
 * 64-bit JVM (016-06/R1, R1-F3).</p>
 * 
 * @author Frans Lundberg
 */
public class KeyNode implements Node {
    public long id;            
        // id is a vpos created by Db when node is created in memory
    public long spos;
        // The stream position of the node when it was last written to the stream.
        // Synch note: see get/set methods. Synched by read/write to volatile field this.size.
    private short lastTimeIndex = -1;
        // -1 or array index to the last time.
        // Synch note: this field should only be accessed by a writer. Access by a reader is not
        // allowed!
    private final boolean isSegmentLeaf;
        // Synch note: final, so we are fine :-)
    public boolean isInTransNodes = false;
        // Synch note: no need for volatile or something since all access is from threads 
        // holding Db.writeLock.
    public int countedMemSize = -1;
        // The size the resident registry counted this object with, the values its pointers
        // hold included, -1 if not counted (bergdb item 001, WP J1; item 009, step 3b;
        // core/Residents.java; 0 before bergdb 015-15). Read and written under the object's
        // monitor.
    private boolean isDirty;
        // Synch note: read/write access only from threads holding Db.writeLock.
    private boolean isCanonical;
        // See Node.isCanonical().
    
    public volatile short size;
        // Size of klong array actually used. 
        // Synch note: Used for synch action between writer and readers. Handles synch for 
        // the arrays too (klongs, pointers, pos).
    public volatile long[] klongs;
        // Synch note: Writes to elements of "klongs" published by a write to this.size. The
        // field is volatile, as pointers and pos, so that a growth's copies are published with
        // the new array (growCapacity; bergdb 015-12, 015-14). Only the writer stores it.
        // Readers should first read this.size, before accessing klongs or elements in klongs.
    
    public volatile Pointee[] pointers;           
        // What each pointer holds (bergdb item 009, step 3a): the handle of a key node it
        // points to, or the ValueNode it points to, or null (not followed yet; a value
        // unswizzled). Before 2026-10-25 the key node objects themselves.
        // Synch note: an element is written under "this" lock with a release store
        // (setPointee, setPointer, swizzle), or by the writer before it publishes a new
        // pointer with this.size, or by the writer's replaceKlong in place, plainly, for a
        // klong of the current transaction, behind its time klong, where every reader stops;
        // read with an acquire (getPointee; 009-02, 3.4; bergdb 015-14). The field is
        // volatile, as klongs.
    public volatile long[] pos;
        // The pointer's reference, its position or vpos (009-02, 4.2): what it named when it
        // was made, loaded, or last resolved. No access data since step 3a.
        // Synch note: an element is written under "this" lock with an opaque store (setRef,
        // raiseRef, setPointer), or by the writer before it publishes a new pointer with
        // this.size, or by replaceKlong, as pointers; a reader reads it with an opaque read
        // after the pointer's acquire (getPointerPos; bergdb 015-14). The field is volatile,
        // as klongs.
    public Handle handle;
        // The handle this object is in, or was in (bergdb item 009, step 3a): set when the
        // object is put into a handle (Cache3.register, install, makeCanonical; Handle.of).

    /** Possible sizes (lengths) of the 'klongs' ('pointers', 'pos') array. */
    private static final int[] ARRAY_SIZES = new int[]{2, 8-2, 16-2, 32-2, 64-2, 128-2};
    
    private static final long[] EMPTY_LONG_ARRAY = new long[0];
    private static final Pointee[] EMPTY_INODE_ARRAY = new Pointee[0];
    
    /**
     * Creates an empty node with zero klongs. isSegmentLeaf is set to true.
     */
    public KeyNode() {
        this(true);
    }
    
    /**
     * Creates an empty node with zero klongs. isDirty is set to false.
     */
    public KeyNode(final boolean isSegmentLeaf) {
        this.isSegmentLeaf = isSegmentLeaf;
        klongs = EMPTY_LONG_ARRAY;
        pointers = EMPTY_INODE_ARRAY;
        pos = EMPTY_LONG_ARRAY;
        spos = Spos.NULL;
        id = Spos.NULL;
        isDirty = false;
        this.size = 0;    
            // Synch action to make constructor writes are visible to others threads that reads the
            // field this.size.
    }
    
    /**
     * Creates a key node with one klong -- a TIME klong.
     * isSegmentLeaf is set to true.
     */
    public static KeyNode nodeWithTime(long time) {
        KeyNode node = new KeyNode(true);
        node.addToEnd(Klong.createTime(time), null, Spos.NULL);
        node.lastTimeIndex = 0;
        assert node.size == 1;
        return node;
    }
    
    public final byte getType() {
        return Node.TYPE_KEY_NODE;
    }
    
    public final boolean isIndexNode() {
        return true;
    }
    
    public final long getSpos() {
        @SuppressWarnings("unused")
        short sz = this.size;       // Synch action to ensure we read last state of spos.
        return this.spos;
    }

    /**
     * Caller must hold DB.writeLock.
     */
    public final void setSpos(long spos) {
        this.spos = spos;
        this.size = this.size;      // Synch action to publish change from writer to readers.
    }
    
    public final boolean isSegmentLeaf() {
        return isSegmentLeaf;
    }
    
    public final boolean isKeyNode() { return true; }
    public final boolean isTopNode() { return false; }
    public final boolean isValueNode() { return false; }
    
    public final boolean isDirty() {
        return isDirty;
    }
    
    public final void setDirty(boolean isDirty) {
        this.isDirty = isDirty;
    }
    
    public final long getKlong(int index) {
        return klongs[index];
    }
    
    public final int getSize() {
        return size;
    }
    
    /**
     * Returns 'size' as it was at the given time.
     */
    public final int getSizeAtTime(long lookupTime) {
        //
        // Not used for product, does not have to be optimized.
        //
        
        final int sz = this.size;
        final long[] klongs = this.klongs;
        long klong;
        int result = sz;
        
        for (int index = 0; index < sz; index++) {
            klong = klongs[index];
            if (Klong.isTime(klong)) {
                long klongTime = Klong.getTime(klong);
                if (klongTime > lookupTime) {
                    result = index;
                    break;
                }
            }
        }
        
        return result;
    }
    
    /**
     * Gets the pointer as one coherent pair (node, pos).
     *
     * <p>2026-10-13 (bergdb 011-04, "Level 3 follow-up"): a reader that follows a stream pointer
     * replaces it by a memory pointer, setting the node and then the position (access data
     * instead of a stream position), while the writer serializes this node. A writer that
     * read the node as null and then the new position took the access data for a stream
     * position and wrote it or failed the check of the serializer ("Bad stream pointer",
     * found by java/stress/ReclaimReaders.java). A memory pointer stays one (no eviction yet), so
     * the common case reads without a lock; a stream pointer is read under the monitor of
     * the node, which setPointer() holds. Level 4 (eviction) must revisit this.</p>
     *
     * <p>2026-10-17 (bergdb item 001, WP R8, change 4: M24 of bergdb 001-08): the
     * reference is read once, and a memory pointer is decided on that read. Its long field is
     * then access data, which no caller takes for a position: once eviction can make a memory
     * pointer a stream pointer again, the field read after the reference can already hold
     * the position.</p>
     */
    public final void getPointer(int index, Pointer pointer) {
        synchronized (this) {
            pointer.node = getPointerNode(index);
            pointer.pos = pos[index];
        }
        pointer.index = index;
    }
    
    /** See Node.getPointerNode(): the value, or the handle's object if it may serve. */
    public final Node getPointerNode(int index) {
        assert index < pointers.length : "bad index, " + index + ", length:" + pointers.length;
        Pointee p = getPointee(index);      // an acquire, then the rest (bergdb 015-14)
        return p == null ? null : nodeOf(p, getPointerPos(index));
    }

    /** What pointee p gives a pointer with reference ref, as getPointerNode. */
    private static Node nodeOf(Pointee p, long ref) {
        if (p instanceof ValueNode) return (ValueNode) p;
        Node o = ((Handle) p).obj;
        return o != null && Handle.usable(o, ref) ? o : null;
    }

    /**
     * A search's result for pointer i (bergdb 015-14): kwi.node as getPointerNode, kwi.pos
     * the reference; the pointer read first, with its acquire, then the reference, each once.
     */
    private void pointerInto(KlongWithPointer kwi, int index) {
        Pointee p = getPointee(index);
        long ref = getPointerPos(index);
        kwi.node = p == null ? null : nodeOf(p, ref);
        kwi.pos = ref;
    }
    
    /**
     * Pointer i's reference, with an opaque read (bergdb 015-14): a reader may read it in a
     * race with a raise, and a plain long may tear (JLS 17.7). A follow reads it after
     * getPointee, whose acquire orders it (009-02, 3.4).
     */
    public final long getPointerPos(int index) {
        return (long) REFS.getOpaque(pos, index);
    }
    
    /**
     * What pointer i holds, read with an acquire (bergdb 015-14; 009-02, 3.4). It pairs with
     * the release store that put the pointee there (setPointee, setPointer, swizzle), so a
     * reader that sees the pointee sees what came before that store: a value's position
     * (ValueNode.spos, volatile but set in the constructor; C5); for a handle, the raise of
     * the pointer's reference and the install of the handle's object before the swizzle.
     * Before 015-14, a pointer to a handle was read plainly (T6b), which left the reader's
     * next reads ordered by the address dependency only (016-06/R1, R1-F3).
     */
    public final Pointee getPointee(int index) {
        return (Pointee) POINTEES.getAcquire(pointers, index);
    }

    private static final VarHandle POINTEES =
            java.lang.invoke.MethodHandles.arrayElementVarHandle(Pointee[].class);
    private static final VarHandle REFS =
            java.lang.invoke.MethodHandles.arrayElementVarHandle(long[].class);
    
    public final void setPointee(int index, Pointee pointee) {
        synchronized (this) {
            // A release store (bergdb item 009, step 3c; 009-02, 3.4): the reader's acquire
            // in getPointee pairs with it, so what came before is visible to the reader: a
            // value's fields (C5); a handle's object and the raised reference (bergdb 015-14).
            POINTEES.setRelease(pointers, index, pointee);
        }
    }
    
    public final void setRef(int index, long ref) {
        synchronized (this) {
            REFS.setOpaque(pos, index, ref);        // atomic, as getPointerPos (015-14)
        }
    }
    
    public final void raiseRef(int index, long ref) {
        synchronized (this) {
            if (Spos.newer(ref, pos[index])) REFS.setOpaque(pos, index, ref);     // as setRef
        }
    }
    
    public final boolean swizzle(int index, Pointee expected, Pointee pointee) {
        synchronized (this) {
            if (pointers[index] != expected) return false;
            POINTEES.setRelease(pointers, index, pointee);      // as setPointee
            return true;
        }
    }
    
    /**
     * Sets a pointer: what it holds and its reference, under the node's monitor (009-02,
     * 3.4, C2).
     */
    public final void setPointer(int index, Pointee pointee, long ref) {
        synchronized (this) {   // See getPointer().
            REFS.setOpaque(pos, index, ref);                    // as setRef
            POINTEES.setRelease(pointers, index, pointee);      // as setPointee
        }
    }
    
    /**
     * See Node.getSerializedRef(). The record rule of 009-02, 4.6 (bergdb item 009, step
     * 3a): a value's position; the canonical object's position if the pointer's handle
     * holds a canonical object; else the newer of the pointer's reference (after Rule R,
     * which the writer applies first, NodeCollection.resolvePointers) and the position this
     * process last wrote the node at (Handle.writtenPos). Read as a coherent pair.
     */
    public final long getSerializedRef(int index) {
        Pointee p;
        long ref;
        synchronized (this) {
            p = pointers[index];
            ref = pos[index];
        }
        return Handle.serializedRef(p, ref);
    }
    
    public void accept(NodeVisitor visitor) {
        visitor.visit(this);
    }
    
    private static final String CLASSNAME = KeyNode.class.getName();
    
    public String toString() {
        String result = super.toString();
        if (result.startsWith(CLASSNAME)) {
            String sub = result.substring(CLASSNAME.length());
            if (sub.length() > 5) {
                sub = sub.substring(sub.length() - 2);
            }
            result = "K/" + sub;
        }
        
        String midPart = (id == -1 && spos == -1) ? "" : " " + id + ":" + spos + "";
        
        result = result + midPart;
        result = isSegmentLeaf ? result + " L" : result;
        return result;
    }
    
    /**
     * Finds an EQUAL match with compareValue; that is, finds a klong that has
     * its compare value == compareValue.
     * If there are multiple matches, the one with the latest time is matched. If there are multiple
     * matches with same compareValue and time, the last one in the klong array (the last one
     * added) is matched. Only klongs with a time >= 'time' are considered.
     * 
     * @param kwi  The result is written to this parameter.
     *      kwi.klong is set to Klong.NULL if no klong was found. On entry, 'kwi' can have any
     *      state.
     */
    public final void searchEq(long time, long compareValue, KlongWithPointer kwi) {
        final int sz; 
        final long[] klongs;
        int index = 0;
        long klong;
        long arrayTime = -1;
        int klongType;
        long deleteBitmap = Klong.DELETE_NONE_BITMAP;
        
        sz = this.size;         // Synch action. Makes changes by writer visible.
        klongs = this.klongs;
        kwi.klong = Klong.NULL;
        
        A: for (index = 0; index < sz; index++) {
            // Not inlined: if (Klong.isDeleted(deleteBitmap, index)) {
            if ((deleteBitmap & Klong.DELETE_BITS[index]) != 0) {
                continue;
            }
            
            klong = klongs[index];
            
            // Not inlined: klongType = Klong.getIntType(klong);
            klongType = (int) ((klong & 0xc000000000000000L) >>> 62);
            
            switch (klongType) {
            case Klong.INT_TYPE_TIME:                
                // Not inlined: arrayTime = Klong.getTime(klong);
                arrayTime = klong & 0x00ffffffffffffffL;
                
                if (arrayTime > time) {
                    break A;  
                    // We are done looping. At time 'time', the rest of the array did not exist.
                }
                break;
            case Klong.INT_TYPE_KEY:
                // Not inlined: if (compareValue == Klong.getCompareValue(klong)) {
                if (compareValue == (klong & 0x3ffffffffffffff8L)) {
                    kwi.klong = klong;
                    kwi.pointerIndex = index;
                    kwi.klongTime = arrayTime;
                    pointerInto(kwi, index);
                }
                break;
            case Klong.INT_TYPE_DELETE_BITMAP:
                deleteBitmap = klong;
                // Not inlined: if (kwi.klong != Klong.NULL && Klong.isDeleted(deleteBitmap, kwi.pointerIndex)) {
                if (kwi.klong != Klong.NULL && (deleteBitmap & Klong.DELETE_BITS[kwi.pointerIndex]) != 0) {
                    kwi.klong = Klong.NULL;
                }
                break;
            default:
                assert false : "Bad klong type, " + klongType;
                break;
            }
        }
    }
    
    /**
     * Finds the largest key klong LTE (<=) compareValue at 'time'.
     * Sets kwi.klong == Klong.NULL if no such klong is found.
     * 
     * @param kwi Used as output parameter. Its state on input does not matter.
     */
    public final void searchLte(long time, long compareValue, KlongWithPointer kwi) {
        //
        // This code is the primary source for searchLTE, searchLT, searchGTE, searchGT.
        // Perf note 2012-06: inlining did not improve performance significantly.
        // Perf note 2012-06: inlining whole method getDeleteBitmapAtTime() did not improve
        //      performance.
        // Note, we count try performance of iterating backwards to avoid two iterations.
        //
        
        final int sz;
        final long[] klongs;
        long klong;
        long arrayTime = -1;
        int klongType;
        long bestCompareValue = -1;         // Best compare value in the matching process so far.
        long bestKlongTime = -1;
        int bestPointerIndex = -1;
        long arrayCompareValue;
        long del = Klong.DELETE_NONE_BITMAP;// Delete klong (bitmap).
        
        sz = this.size;                     // Synch action. Makes changes by writer visible.
        klongs = this.klongs;
        kwi.klong = Klong.NULL;
        
        del = this.getDeleteBitmapAtTime(time, sz);
        
        A: for (int i = 0; i < sz; i++) {
            
            // Not inlined: if (Klong.isDeleted(del, i)) {
            if ((del & Klong.DELETE_BITS[i]) != 0) {
                continue;
            }
            
            klong = klongs[i];
            // Not inlined: klongType = Klong.getIntType(klong);
            klongType = (int) ((klong & 0xc000000000000000L) >>> 62);
            
            switch (klongType) {
            case Klong.INT_TYPE_TIME:
                // No inlined: arrayTime = Klong.getTime(klong);
                arrayTime = klong & 0x00ffffffffffffffL;
                
                if (arrayTime > time) {
                    break A;
                }
                break;
            case Klong.INT_TYPE_KEY:
                // Not inlined: arrayCompareValue = Klong.getCompareValue(klong);
                arrayCompareValue = klong & 0x3ffffffffffffff8L;
                
                if (arrayCompareValue >= bestCompareValue && arrayCompareValue <= compareValue) {
                    bestCompareValue = arrayCompareValue;
                    bestPointerIndex = i;
                    bestKlongTime = arrayTime;
                }
                break;
            case Klong.INT_TYPE_DELETE_BITMAP:
                // Empty
                break;
            default:
                assert false : "Bad klong type, " + klongType;
                break;
            }
        }
        
        if (bestCompareValue != -1) {
            kwi.klong = klongs[bestPointerIndex];
            kwi.pointerIndex = bestPointerIndex;
            kwi.klongTime = bestKlongTime;
            pointerInto(kwi, bestPointerIndex);
        }
    }
    
    /**
     * Finds the largest key klong LT (<) compareValue at 'time'.
     * Sets kwi.klong == Klong.NULL if no such klong is found.
     * 
     * @param kwi Used as output parameter. Its state on input does not matter.
     */
    public final void searchLt(long time, long compareValue, KlongWithPointer kwi) {
        //
        // Code copied from searchLTE.
        //
        
        final int sz;
        final long[] klongs;
        long klong;
        long arrayTime = -1;
        int klongType;
        long bestCompareValue = -1;         // Best compare value in the matching process so far.
        long bestKlongTime = -1;
        int bestPointerIndex = -1;
        long arrayCompareValue;
        long del = Klong.DELETE_NONE_BITMAP; // Delete klong (bitmap).
        
        sz = this.size;
        klongs = this.klongs;
        kwi.klong = Klong.NULL;
        
        del = this.getDeleteBitmapAtTime(time, sz);
        
        A: for (int i = 0; i < sz; i++) {
            
            // Not inlined: if (Klong.isDeleted(del, i)) {
            if ((del & Klong.DELETE_BITS[i]) != 0) {
                continue;
            }
            
            klong = klongs[i];
            // Not inlined: klongType = Klong.getIntType(klong);
            klongType = (int) ((klong & 0xc000000000000000L) >>> 62);
            
            switch (klongType) {
            case Klong.INT_TYPE_TIME:
                // No inlined: arrayTime = Klong.getTime(klong);
                arrayTime = klong & 0x00ffffffffffffffL;
                
                if (arrayTime > time) {
                    break A;
                }
                break;
            case Klong.INT_TYPE_KEY:
                // Not inlined: arrayCompareValue = Klong.getCompareValue(klong);
                arrayCompareValue = klong & 0x3ffffffffffffff8L;
                
                // Note: code copied from searchLTE, only a single '=' removed in line below.
                if (arrayCompareValue >= bestCompareValue && arrayCompareValue < compareValue) {
                    bestCompareValue = arrayCompareValue;
                    bestPointerIndex = i;
                    bestKlongTime = arrayTime;
                }
                break;
            case Klong.INT_TYPE_DELETE_BITMAP:
                // Empty
                break;
            default:
                assert false : "Bad klong type, " + klongType;
                break;
            }
        }
        
        if (bestCompareValue != -1) {
            kwi.klong = klongs[bestPointerIndex];
            pointerInto(kwi, bestPointerIndex);
            kwi.pointerIndex = bestPointerIndex;
            kwi.klongTime = bestKlongTime;
        }
    }
    
    /**
     * Finds the smallest key klong GT (>) compareValue at 'time'.
     * Sets kwi.klong == Klong.NULL if no such klong is found.
     * 
     * @param compareValue  The compare value to compare array klongs with. Use -1 to find
     * the smallest key klong.
     * @param kwi Used as output parameter. Its state on input does not matter.
     */
    public final void searchGt(long time, long compareValue, KlongWithPointer kwi) {
        final int sz;
        final long[] klongs;
        long klong;
        long arrayTime = -1;
        int klongType;
        long bestCompareValue = -1;         // Best compare value in the matching process so far.
        long bestKlongTime = -1;
        int bestPointerIndex = -1;
        long arrayCompareValue;
        long del = Klong.DELETE_NONE_BITMAP; // Delete klong (bitmap).
        
        sz = this.size;
        klongs = this.klongs;
        kwi.klong = Klong.NULL;
        
        del = this.getDeleteBitmapAtTime(time, sz);
        
        A: for (int i = 0; i < sz; i++) {
            
            // Not inlined: if (Klong.isDeleted(del, i)) {
            if ((del & Klong.DELETE_BITS[i]) != 0) {
                continue;
            }
            
            klong = klongs[i];
            // Not inlined: klongType = Klong.getIntType(klong);
            klongType = (int) ((klong & 0xc000000000000000L) >>> 62);
            
            switch (klongType) {
            case Klong.INT_TYPE_TIME:
                // No inlined: arrayTime = Klong.getTime(klong);
                arrayTime = klong & 0x00ffffffffffffffL;
                
                if (arrayTime > time) {
                    break A;
                }
                break;
            case Klong.INT_TYPE_KEY:
                // Not inlined: arrayCompareValue = Klong.getCompareValue(klong);
                arrayCompareValue = klong & 0x3ffffffffffffff8L;
                
                if ((arrayCompareValue <= bestCompareValue || bestCompareValue == -1) 
                        && arrayCompareValue > compareValue) {
                    bestCompareValue = arrayCompareValue;
                    bestPointerIndex = i;
                    bestKlongTime = arrayTime;
                }
                break;
            case Klong.INT_TYPE_DELETE_BITMAP:
                // Empty
                break;
            default:
                assert false : "Bad klong type, " + klongType;
                break;
            }
        }
        
        if (bestCompareValue != -1) {
            kwi.klong = klongs[bestPointerIndex];
            pointerInto(kwi, bestPointerIndex);
            kwi.pointerIndex = bestPointerIndex;
            kwi.klongTime = bestKlongTime;
        }
    }
    
    /**
     * Finds the smallest key klong GTE compareValue at 'time'.
     * Sets kwi.klong == Klong.NULL if no such klong is found.
     * 
     * @param compareValue  The compare value to compare array klongs with. Use -1 to find
     * the smallest key klong.
     * @param kwi Used as output parameter. Its state on input does not matter.
     */
    public final void searchGte(long time, long compareValue, KlongWithPointer kwi) {
        final int sz;
        final long[] klongs;
        long klong;
        long arrayTime = -1;
        int klongType;
        long bestCompareValue = -1;         // Best compare value in the matching process so far.
        long bestKlongTime = -1;
        int bestPointerIndex = -1;
        long arrayCompareValue;
        long del = Klong.DELETE_NONE_BITMAP; // Delete klong (bitmap).
        
        sz = this.size;
        klongs = this.klongs;
        kwi.klong = Klong.NULL;
        
        del = this.getDeleteBitmapAtTime(time, sz);
        
        A: for (int i = 0; i < sz; i++) {
            
            // Not inlined: if (Klong.isDeleted(del, i)) {
            if ((del & Klong.DELETE_BITS[i]) != 0) {
                continue;
            }
            
            klong = klongs[i];
            // Not inlined: klongType = Klong.getIntType(klong);
            klongType = (int) ((klong & 0xc000000000000000L) >>> 62);
            
            switch (klongType) {
            case Klong.INT_TYPE_TIME:
                // No inlined: arrayTime = Klong.getTime(klong);
                arrayTime = klong & 0x00ffffffffffffffL;
                
                if (arrayTime > time) {
                    break A;
                }
                break;
            case Klong.INT_TYPE_KEY:
                // Not inlined: arrayCompareValue = Klong.getCompareValue(klong);
                arrayCompareValue = klong & 0x3ffffffffffffff8L;
                
                if ((arrayCompareValue <= bestCompareValue || bestCompareValue == -1) 
                        && arrayCompareValue >= compareValue) {
                    bestCompareValue = arrayCompareValue;
                    bestPointerIndex = i;
                    bestKlongTime = arrayTime;
                }
                break;
            case Klong.INT_TYPE_DELETE_BITMAP:
                // Empty
                break;
            default:
                assert false : "Bad klong type, " + klongType;
                break;
            }
        }
        
        if (bestCompareValue != -1) {
            kwi.klong = klongs[bestPointerIndex];
            pointerInto(kwi, bestPointerIndex);
            kwi.pointerIndex = bestPointerIndex;
            kwi.klongTime = bestKlongTime;
        }
    }
    
    public final void searchFirst(long time, KlongWithPointer kwi) {
        final int sz;
        final long[] klongs;
        long klong;
        long arrayTime = -1;
        int klongType;
        long bestCompareValue = -1;         // Best compare value in the matching process so far.
        long bestKlongTime = -1;
        int bestPointerIndex = -1;
        long arrayCompareValue;
        long del = Klong.DELETE_NONE_BITMAP; // Delete klong (bitmap).
        
        sz = this.size;                     // Synch action, makes writes visible.
        klongs = this.klongs;
        kwi.klong = Klong.NULL;
        
        del = this.getDeleteBitmapAtTime(time, sz);
        
        A: for (int i = 0; i < sz; i++) {
            
            // Not inlined: if (Klong.isDeleted(del, i)) {
            if ((del & Klong.DELETE_BITS[i]) != 0) {
                continue;
            }
            
            klong = klongs[i];
            // Not inlined: klongType = Klong.getIntType(klong);
            klongType = (int) ((klong & 0xc000000000000000L) >>> 62);
            
            switch (klongType) {
            case Klong.INT_TYPE_TIME:
                // No inlined: arrayTime = Klong.getTime(klong);
                arrayTime = klong & 0x00ffffffffffffffL;
                
                if (arrayTime > time) {
                    break A;
                }
                break;
            case Klong.INT_TYPE_KEY:
                // Not inlined: arrayCompareValue = Klong.getCompareValue(klong);
                arrayCompareValue = klong & 0x3ffffffffffffff8L;
                
                if (arrayCompareValue < bestCompareValue || bestCompareValue == -1) {
                    bestCompareValue = arrayCompareValue;
                    bestPointerIndex = i;
                    bestKlongTime = arrayTime;
                }
                break;
            case Klong.INT_TYPE_DELETE_BITMAP:
                // Empty
                break;
            default:
                assert false : "Bad klong type, " + klongType;
                break;
            }
        }
        
        if (bestCompareValue != -1) {
            kwi.klong = klongs[bestPointerIndex];
            pointerInto(kwi, bestPointerIndex);
            kwi.pointerIndex = bestPointerIndex;
            kwi.klongTime = bestKlongTime;
        }
    }
    
    public void addDeleteKlong(long time, long klong) {
        assert Klong.getType(klong) == Klong.TYPE_DELETE_BITMAP;
        addKlong(time, klong, null, Spos.NULL);
    }
    
    /**
     * Adds a klong with a pointer/null and accessData/spos to the end of the key node.
     * If needed, a time klong is added before 'klong'.
     */
    public void addKlong(long time, long klong, Node pointerNode, long accessDataOrSpos) {
        // A pointer to a node holds its handle, or the value; its reference is the node's
        // position, its vpos if not written (bergdb item 009, step 3a). Without a node, a
        // stream pointer: accessDataOrSpos is its position.
        final Pointee pointer = Handle.pointeeOf(pointerNode);
        final long ref = pointerNode != null ? pointerNode.getSpos() : accessDataOrSpos;
        short sz;
        
        // Synch action, ensures that published previous writes are visible.
        sz = this.size;             
        
        assert lastTimeIndex == -1 || time >= klongs[lastTimeIndex] : 
            "lastTimeIndex=" + lastTimeIndex + ", lastTime: " + klongs[lastTimeIndex] 
            + ", time=" + time + ", keyNode: " + this.print();
        assert Klong.getType(klong) != Klong.TYPE_TIME : "Time klongs not supported.";
        
        int addCount = 1;
        if (lastTimeIndex == -1 || time > Klong.getTime(klongs[lastTimeIndex])) {
            addCount = 2;
        }
        
        ensureCapacity(sz + addCount);
        
        assert this.klongs.length >= sz + addCount : "bad ensureCapacity " 
                + this.klongs.length + ", " + addCount + ", " + sz;
        
        short newSize = sz;
        
        if (addCount == 2) {
            // Adds a time klong.
            this.klongs[newSize] = Klong.createTime(time);
            this.pointers[newSize] = null;
            this.pos[newSize] = Spos.NULL;     // Important that pos==NULL here, no pointer.
            this.lastTimeIndex = newSize;
            newSize++;
        }
        
        assert this.klongs.length > newSize : "klongs.length=" + klongs.length 
                + ", mySize=" + newSize;
        
        this.klongs[newSize] = klong;
        this.pointers[newSize] = pointer;
        this.pos[newSize] = ref;
        newSize++;
        
        // Synch action, line below makes changes visible to readers (that read this.size).
        this.size = newSize;
    }
    
    /**
     * Replaces existing key klong along with pointer and accessData if
     * 'klong' equals an existing key klong at the same time.
     * Delete klongs are not allowed in this KeyNode.
     * 
     * @return true if a klong was replaced.
     */
    public boolean replaceKlong(long time, long klong1, Node pointerNode, long accessData) {
        final Pointee pointer = Handle.pointeeOf(pointerNode);
        final long ref = pointerNode != null ? pointerNode.getSpos() : accessData;
        final int sz; 
        final long[] klongs;
        int index = 0;
        long klong; 
        long arrayTime = -1;
        int klongType;
        boolean result = false;
        
        sz = this.size;         // Synch action. Makes changes by writer visible.
        klongs = this.klongs;
        
        A: for (index = 0; index < sz; index++) {
            klong = klongs[index];
            klongType = Klong.getIntType(klong);
            
            switch (klongType) {
            case Klong.INT_TYPE_TIME:                
                arrayTime = Klong.getTime(klong);
                break;
            case Klong.INT_TYPE_KEY:
                if (klong1 == klong && time == arrayTime) {
                    this.klongs[index] = klong1;
                    this.pointers[index] = pointer;
                    this.pos[index] = ref;
                    result = true;
                    break A;
                }
                break;
            case Klong.INT_TYPE_DELETE_BITMAP:
                throw new IllegalStateException("This method is cannot be used for "
                        + "KeyNode with delete klongs.");
            default:
                throw new IllegalStateException("unexpected klong type, " + klongType);
            }
        }
        return result;
    }
    
    /**
     * Write access required.
     * Array replacement shares the node monitor with reader swizzling. The caller still
     * publishes new logical entries to other threads by writing to this.size.
     */
    private void ensureCapacity(int neededSize) {
        if (neededSize <= klongs.length) {
            return;
        }
        // Readers swizzle under this monitor. Copy and publish all pointer arrays
        // together so a swizzle cannot be split across the old and new arrays.
        synchronized (this) {
            growCapacity(neededSize);
        }
    }

    private void growCapacity(int neededSize) {
        assert Thread.holdsLock(this);
        int sz = this.size;
        
        assert sz <= klongs.length;
        
        if (neededSize > klongs.length) {
            int newSize = -1;
            final int arraySizesLength = KeyNode.ARRAY_SIZES.length;
            for (int i = 0; i < arraySizesLength; i++) {
                int arraySize = KeyNode.ARRAY_SIZES[i];
                if (arraySize >= neededSize) {
                    newSize = arraySize;
                    break;
                }
            }
            
            if (newSize == -1) {
                newSize = neededSize + 10;
            }
            
            long[] klongs = new long[newSize];
            Pointee[] pointers = new Pointee[newSize];
            long[] pos = new long[newSize];
            
            System.arraycopy(this.klongs, 0, klongs, 0, sz);
            System.arraycopy(this.pointers, 0, pointers, 0, sz);
            System.arraycopy(this.pos, 0, pos, 0, sz);
            
            // The copies before the new arrays (bergdb 015-12, 015-14): a reader that read size
            // before this growth can read the fields after it. The fields are volatile: their
            // stores come after the copies, so a reader whose volatile read of a field sees a
            // new array sees its copies (JLS 17.4.5). In 015-12, a release fence before plain
            // stores, whose reader side rested on the address dependency.
            this.klongs = klongs;
            this.pointers = pointers;
            this.pos = pos;
        }
    }
    
    /**
     * Adds a klong and its pointer to the end of the arrays.
     * No checking is used. Write access required.
     */
    public void addToEnd(long klongToAdd, Pointee pointerToAdd, long posToAdd) {
        int sz = this.size;             // Synch action make previous writes visible.
        if (klongs.length + 1 > sz) {
            ensureCapacity(sz + 1);
        }
        
        if (Klong.getType(klongToAdd) == Klong.TYPE_TIME) {
            this.lastTimeIndex = (short) sz;
        }
        
        klongs[sz] = klongToAdd;
        pointers[sz] = pointerToAdd;
        pos[sz] = posToAdd;
        
        this.size = (short) (sz + 1);  // Synch action that publishes the changes to readers.
    }
    
    /**
     * Changes the state of this node to the state it was at the given database time.
     * Klongs with time <= 'time' are retained, while klongs with a higher time are discarded.
     * Lowers the size; see the class comment for when that is safe with concurrent readers.
     */
    public void toPreviousState(long time) {
        short sz = this.size;
        
        A:
        for (int i = 0; i < sz; i++) {
            long klong = klongs[i];
            
            if (Klong.getIntType(klong) == Klong.INT_TYPE_TIME) {
                long klongTime = Klong.getTime(klong);
                if (klongTime > time) {
                    if (i == 0) {
                        this.size = 0;
                    } else {
                        this.size = (short) i;
                    }
                    break A;
                }
            }
        }
        
        this.lastTimeIndex = -1;
    }
    
    /**
     * Replaces the content of this node by the content of 'other'. Write access required.
     * Only for a node with no klongs before the current transaction, and an 'other' whose
     * first klong is the time klong of the transaction: readers see none of the klongs, see
     * the class comment. Used to split such a node in place (Dag.handleFullNode).
     */
    void setContentFrom(KeyNode other) {
        assert other.size > 0 && Klong.getType(other.klongs[0]) == Klong.TYPE_TIME;
        int sz = other.size;
        int len = Math.max(sz, other.klongs.length);
        long[] k = new long[len];
        Pointee[] p = new Pointee[len];
        long[] ps = new long[len];
        System.arraycopy(other.klongs, 0, k, 0, sz);
        System.arraycopy(other.pointers, 0, p, 0, sz);
        System.arraycopy(other.pos, 0, ps, 0, sz);
        
        // The copies before the new arrays, as in growCapacity (bergdb 015-12, 015-14): a
        // reader that read the old size can read the fields after this, and must see the
        // first klong, the time klong of the transaction, where it stops. The fields are
        // volatile, and stored after the copies.
        
        // The same monitor as ensureCapacity(): a reader that swizzles a pointer must not see
        // the old pointer arrays with the new klongs.
        synchronized (this) {
            this.klongs = k;
            this.pointers = p;
            this.pos = ps;
            this.lastTimeIndex = other.lastTimeIndex;
        }
        this.size = (short) sz;         // Synch action that publishes the changes to readers.
    }
    
    /**
     * Returns a new key node that is the last version of this node. The returned node has a 
     * klong array that is sorted in strictly increasing compare value order.
     * 
     * @param time The time to get the last version.
     */
    public final KeyNode lastVersion(long time) {
        short sz = this.size;
        long deleteBitmap = this.getLastDeleteBitmap(sz);
        return lastVersionGivenDel(sz, time, deleteBitmap);
    }

    /**
     * Returns a new key node that is the last version of this node. The returned node has a 
     * klong array that is sorted in strictly increasing compare value order.
     * 
     * @param time  The time to get the last version.
     * @param del  The delete klong to use.
     */
    public synchronized KeyNode lastVersionGivenDel(final short sz, long time, long del) {
        // A reader may swizzle an existing slot while the writer takes this copy.
        // Hold the same monitor as setPointer() for both fields of every copied edge.
        //
        // A simple brute-force method that scales with n^2, n = this.size.
        // Likely still faster than sorting first because of limited size.
        //
        
        KeyNode result;
        
        assert sz >= 0 && sz <= 62 : "sz not in range: " + sz;
        
        result = new KeyNode(this.isSegmentLeaf);
        result.ensureCapacity(1 + sz - timeKlongCount(sz));
        
        // Note, actual result size may be smaller because of deletes or setting a key klong
        // several times.
        
        result.addToEnd(Klong.createTime(time), null, Spos.NULL);
        assert result.lastTimeIndex == 0;
        
        A: for (int i = 0; i < sz; i++) {
            if (Klong.isDeleted(del, i)) {
                continue A;
            }
            
            long klong1 = klongs[i];
            long type = Klong.getType(klong1);
            if (type == Klong.TYPE_DELETE_BITMAP) {
                continue A;   // Just continue, we know delete bitmap already
            }
            
            long klongToAdd = Klong.NULL;
            Pointee pointerToAdd = null;
            long posToAdd = Spos.NULL;
    
            if (type == Klong.TYPE_TIME) {
                if (Klong.getTime(klong1) > time) {
                    // Rest of klongs have a too high time, break for loop.
                    break A;
                } else {
                    // Skips the time klong.
                    continue A;
                }
            }
            
            assert type == Klong.TYPE_KEY;
            
            long compareValue1 = Klong.getCompareValue(klong1);
            
            // If such a compareValue is already in result, do nothing with this klong;
            // it has been handled already. Go to next one [continue A;].
            
            for (int j = 0; j < result.size; j++) {
                long k1 = result.klongs[j];
                if (Klong.getType(k1) == Klong.TYPE_KEY 
                        && Klong.getCompareValue(k1) == compareValue1) {
                    continue A;
                }
            }
            
            klongToAdd = klongs[i];
            pointerToAdd = pointers[i];     // Reference is copied, no deep copy.
            posToAdd = pos[i];

            // We have a klong with a compareValue that does not exist in result, 
            // lets see if it is modified (set again) in the rest of the array (within 
            // the time boundry).
            
            for (int j = i + 1; j < sz; j++) {
                
                if (Klong.isDeleted(del, j)) {
                    continue;
                }
                
                long klong2 = klongs[j];
                int intType2 = Klong.getIntType(klong2);
                
                switch (intType2) {
                case Klong.INT_TYPE_TIME:
                case Klong.INT_TYPE_DELETE_BITMAP:
                    continue;
                case Klong.INT_TYPE_KEY:
                    long cValue = Klong.getCompareValue(klong2);
                    if (cValue == compareValue1) {
                        klongToAdd = klong2;
                        pointerToAdd = pointers[j];
                        posToAdd = pos[j];
                    }
                    break;
                default:
                    assert false : "Bad klong type, " + intType2 + ".";
                    break;
                }
            }
            
            if (klongToAdd != Klong.NULL) {
                result.addToSorted(klongToAdd, pointerToAdd, posToAdd);
            }
        }
        
        return result;
    }
    
    /**
     * Special method that adds a klong to an already sorted key node.
     * 'this.klongs' is assumed to be sorted in strictly increasing compareValue order.
     * Zero or one time klong is allowed. If there is one, it must be the first klong.
     * It is also assumed that there is no delete klong in 'this.klongs'.
     * Write access required. Additionally, no readers can access 'this' while the method
     * is executing.
     * 
     * @param klongToAdd The klong to add must be of type Klong.TYPE_KEY.
     * @param pointerToAdd
     * @param posToAdd
     */
    private void addToSorted(long klongToAdd, Pointee pointerToAdd, long posToAdd) {
        assert Klong.getType(klongToAdd) == Klong.TYPE_KEY;
        
        long compareValue = Klong.getCompareValue(klongToAdd);
        short sz = this.size;
        ensureCapacity(sz + 1);
        int startIndex = 0;
        if (sz > 0 && Klong.getType(klongs[0]) == Klong.TYPE_TIME) {
            startIndex = 1;
        }
        
        boolean added = false;
        
        for (int i = startIndex; i < sz; i++) {
            long arrayCompareValue = Klong.getCompareValue(klongs[i]);
            if (arrayCompareValue == compareValue) {
                // If same compare value, overwrite (will this ever happen?)
                klongs[i] = klongToAdd;
                pointers[i] = pointerToAdd;
                pos[i] = posToAdd;
                added = true;
                break;
            } else if (arrayCompareValue > compareValue) {
                // Move existing values in the arrays to the right one step. Then insert.
                System.arraycopy(klongs, i, klongs, i + 1, sz - i);
                System.arraycopy(pointers, i, pointers, i + 1, sz - i);
                System.arraycopy(pos, i, pos, i + 1, sz - i);
                klongs[i] = klongToAdd;
                pointers[i] = pointerToAdd;
                pos[i] = posToAdd;
                this.size = (short) (sz + 1);
                added = true;
                break;
            }
        }
        
        if (!added) {
            // Adds to end if not already added. klongToAdd > all-existing-klongs-in-array.
            klongs[sz] = klongToAdd;
            pointers[sz] = pointerToAdd;
            pos[sz] = posToAdd;
            this.size = (short) (sz + 1);
            added = true;
        }
    }
    
    /**
     * Returns number of time klongs in this.klongs given that its size is sz.
     */
    private int timeKlongCount(int sz) {
        int timeCount = 0;
        
        for (int i = 0; i < sz; i++) {
            long k = klongs[i];
            if (Klong.getType(k) == Klong.TYPE_TIME) {
                timeCount++;
            }
        }
        return timeCount;
    }
    
    /**
     * Splits this node into two: first and second.
     * Inserts the klongs in 'insert' into either 'first' or 'second'.
     * 
     * @param tTime  The transaction time of the insert.
     * @param last  Last version of the node that is full (node.lastVersion()).
     * @param insert  The kwis to insert. Must be of non-zero length. Always 1 or 2 long, I believe.
     */
    public long firstAndSecond(long tTime, KeyNode last, KlongWithPointer[] insert, KeyNode first, 
            KeyNode second) {
        assert insert != null;
        assert insert.length >= 0 && insert.length < 10 : "Bad insert.length " + insert.length + ".";
        
        int lastSize = last.size;
        int sizeOfFirst = (lastSize - 1) / 2 + 1;
        assert Klong.getType(last.klongs[0]) == Klong.TYPE_TIME;
        assert lastSize > 1 : "last.size=" + lastSize + ", this.size=" + this.size 
            + "\n-- This node:\n" + this.print() + "-- Last version node:\n" + last.print();
        assert last.checkWithMessage() == null : last.checkWithMessage();
        
        long timeKlong = Klong.createTime(tTime);
        first.addToEnd(timeKlong, null, Spos.NULL);       // time klong, spos should be NULL
        second.addToEnd(timeKlong, null, Spos.NULL);      // time klong, spos should be NULL
        long secondKlong = Klong.NULL;
        
        for (int i = 1; i < lastSize; i++) {
            assert Klong.getType(last.klongs[i]) != Klong.TYPE_TIME : "Unexpected time klong, " 
                    + Klong.getTime(last.klongs[i]);
            if (first.size < sizeOfFirst) {
                first.addToEnd(last.klongs[i], last.pointers[i], last.pos[i]);
            } else {
                second.addToEnd(last.klongs[i], last.pointers[i], last.pos[i]);
                if (secondKlong == Klong.NULL) {
                    secondKlong = last.klongs[i];
                }
            }
        }
        
        assert secondKlong != Klong.NULL;
        assert first.size > 0;
        assert second.size > 0;
        
        KeyNode insertTo = first;
        if (insert.length > 0 && Klong.getCompareValue(insert[0].klong) >= Klong.getCompareValue(secondKlong)) {
            insertTo = second;
        }
        
        for (int i = 0; i < insert.length; i++) {
            KlongWithPointer kwi = insert[i];
            insertTo.addToEnd(kwi.klong, Handle.pointeeOf(kwi.node),
                    kwi.node != null ? kwi.node.getSpos() : kwi.pos);
        }
        
        return secondKlong;
    }
    
    public final int getMemSize() {
        //
        // * 16 - overhead for any object.
        // * 16 - non-array fields
        // * klongs/pointers/pos, 8 + 8 + 8 time size of array. Plus 16 per array as overhead.
        //   (16*3 + 8*klongs.length + 8*pointers.length + 8*pos.length).
        // 
        // All arrays are of same length, so we can simplify to:
        //   16 + 16 + 16*3 + klongs.length*(3*8).
        // = 80 + klongs.length * 24; 
        //
        
        return 80 + klongs.length * 24;
    }
    
    /**
     * Does not require write access.
     */
    public int getMemoryPointerCount() {
        int count = 0;
        int size = this.size;
        for (int i = 0; i < size; i++) {
            if (getPointerNode(i) != null) count++;
        }
        return count;
    }

    public final long getId() {
        return id;
    }

    public final void setId(long id) {
        this.id = id;
    }

    /**
     * Caller must hold DB.writeLock.
     */
    public final boolean isInTransNodes() {
        // 130117 Frans. Only called from code holding DB.writeLock.
        return isInTransNodes;
    }

    public final boolean isCanonical() {
        return isCanonical;
    }
    
    public final void setCanonical(boolean isCanonical) {
        this.isCanonical = isCanonical;
    }

    /**
     * Caller must hold DB.writeLock.
     */
    public final void setIsInTransNodes(boolean b) {
        // 130117 Frans. Only called from code holding DB.writeLock.
        this.isInTransNodes = b;
    }

    /**
     * Return a multi-line string describing the key node. For debug.
     */
    public String print() {
        return print("");
    }
    
    /**
     * Return a multi-line string describing the key node. For debug.
     * 
     * @param indent  The spaces or something else to indent the text with.
     */
    public String print(String indent) {
        ByteArrayOutputStream bout = new ByteArrayOutputStream();
        PrintStream out = new PrintStream(bout);
        printInternal(out, indent, 0, false);
        return StringUtil.toString(bout.toByteArray());
    }
    
    /**
     * Prints node to a PrintStream. Can recurse to print tree.
     */
    void printInternal(PrintStream out, String indent, int depth, boolean printChildren) {
        int size = this.size;
        String newIndent = "    " + indent;
        
        if (depth > 10) {
            out.println(indent + "<depth limit reached>...");
            return;
        }
        out.println(indent + this.toString());
        //if (size == 0) {
        //    out.println(indent + "no klongs");
        //}
        
        for (int i = 0; i < size; i++) {
            long klong = klongs[i];
            int type = Klong.getIntType(klong);
            
            out.print(indent + String.format("%02d", i) + ": ");
            
            switch (type) {
            case Klong.INT_TYPE_TIME:
                long arrayTime = Klong.getTime(klong);
                out.println("TIME:" + arrayTime);
                break;
                
            case Klong.INT_TYPE_KEY:
                String keyString = getKeyString(klong);
                out.print(String.format("%-15s", keyString));
                Node child = getPointerNode(i);
                boolean isMem = child != null;
                
                if (isMem) {
                    if (printChildren && (child instanceof KeyNode)) {
                        KeyNode keyNodeChild = (KeyNode) child;
                        out.print(" ->\n");
                        keyNodeChild.printInternal(out, newIndent, depth + 1, true);
                        
                    } else {
                        out.println(" -> " + child.toString());
                    }
                } else {
                    out.println(" -> spos: " + pos[i]);
                }
                break;
                
            case Klong.INT_TYPE_DELETE_BITMAP:
                out.println(Klong.toString(klong));
                break;
                
            default:
                assert false : "bad klong type " + type;
                break;
            }
        }
    }
    
    private static String getKeyString(long klong) {
        byte[] bytes = new byte[Klong.getLength(klong)];
        Klong.getKey(klong, bytes);
        return getKeyString(bytes);
    }
    
    /**
     * For printing, debug. Prints value of key klong: as text if its bytes are printable
     * ASCII, each less 2, else in hexadecimal. The text is Keys.toDisplayString()'s, as
     * Klong.getKeyString() shows a klong: a key with the byte 0x31 ('/' + 2), as an index
     * entry's level may have, has no ikey, and Keys.bkey2ikey() throws for it (bergdb 021-06).
     */
    public static String getKeyString(byte[] bytes) {
        // Assumes bytes created from ukey.
        
        String result;
        
        if (bytes == null) {
            result = "null";
        } else {
            if (Keys.isPrintableAscii(bytes)) {
                result = Keys.toDisplayString(bytes);
            } else {
                result = "#" + StringUtil.toHex(bytes);
            }
        }
        
        return result;
    }
    
    void getInfo(NodeInfo info) {
        long arrayTime = 0;
        long klong;
        long compareValue;
        int type;
        int uniqueKeyCount = 0;
        long lastCompareValue = 0L;
        
        info.klongCount = 0;
        info.timeCount = 0;
        info.deleteCount = 0;
        info.lastTime = -1;
        
        KlongIter iter = createKlongIter();
        
        while (iter.hasNext()) {
            klong = iter.next();
            info.klongCount++;
            type = Klong.getIntType(klong);
            compareValue = Klong.getCompareValue(klong);
            
            switch (type) {
            case Klong.INT_TYPE_TIME:
                arrayTime = Klong.getTime(klong);
                info.timeCount++;
                info.lastTime = arrayTime;
                break;
            case Klong.INT_TYPE_KEY:
                if (compareValue != lastCompareValue) {
                    uniqueKeyCount++;
                }
                lastCompareValue = klong;
                break;
            case Klong.INT_TYPE_DELETE_BITMAP:
                if (compareValue != lastCompareValue) {
                    uniqueKeyCount++;
                }
                lastCompareValue = klong;
                info.deleteCount++;
                break;
            }
        }
        
        info.uniqueKeyCount = uniqueKeyCount;
    }
    
    public boolean assertOk(int maxNodeSize) {
        check(maxNodeSize);
        return true;
    }
    
    /**
     * Same as check() except for that the node size is also checked against maxNodeSize.
     */
    public void check(int maxNodeSize) {
        short sz = this.size;
        if (sz > maxNodeSize + 1) {
            throw new AssertionError("Overfull node, size=" + sz + ", maxNodeSize=" + maxNodeSize + ", KeyNode: " + toString());
        }
        
        check();
    }
    
    /**
     * Checks the state of the node and throws AssertionError if
     * is is not in a consistent state. There are a number of invariants.
     * Write access required (since this.lastTimeIndex is used).
     * This method is not performant, could be much faster.
     */
    public void check() {
        short sz = this.size;
        checkSizes();
        checkLastTimeIndex();
        checkIncreasingTime();
        checkMemoryPointers(sz);
        checkStreamPointers(sz);
    }

    // The two checks below read a pointer's pair under the node's monitor, which a reader that
    // swizzles the pointer holds (setPointer): read apart, the reference and the long field of
    // a pointer being swizzled could be one old and one new, which the checks took for a bad
    // pointer (bergdb item 001, WP J5: java/stress/ReclaimReaders.java with eviction, where
    // readers swizzle the current nodes' pointers after every transaction; before
    // 2026-10-18 unsynchronized, a race the writer's assertions could lose after a restart too).

    private void checkStreamPointers(short sz) throws AssertionError {
        for (int i = 0; i < sz; i++) {
            long klong = klongs[i];
            if (Klong.getType(klong) == Klong.TYPE_KEY) {
                Pointee pointer;
                long spos;
                synchronized (this) {
                    pointer = pointers[i];
                    spos = pos[i];
                }
                if (pointer == null) {
                    if (!Spos.isValid(spos)) {
                        throw new AssertionError("Bad spos of pointer " + i + " of node " 
                                + this + ". Spos: " + spos);
                    }
                }
            }
        }
    }

    private void checkMemoryPointers(short sz) throws AssertionError {
        for (int i = 0; i < sz; i++) {
            long klong = klongs[i];
            if (Klong.getType(klong) == Klong.TYPE_KEY) {
                Pointee pointer;
                long ref;
                synchronized (this) {
                    pointer = pointers[i];
                    ref = pos[i];
                }
                if (pointer != null) {
                    // A pointer that holds a handle or a value has a reference too (bergdb
                    // item 009, step 3a; before, access data).
                    if (!Spos.isValidOrNull(ref)) {
                        throw new AssertionError("Bad reference (" + ref 
                                + ") of pointer " + i + " of node " + this + ".");
                    }
                }
            }
        }
    }

    private void checkIncreasingTime() throws AssertionError {
        long time = Long.MIN_VALUE;
        short sz = this.size;
        
        for (int i = 0; i < sz; i++) {
            long klong = klongs[i];
            if (Klong.getType(klong) == Klong.TYPE_TIME) {
                long klongTime = Klong.getTime(klong);
                if (klongTime <= time) {
                    throw new AssertionError("Time not increasing, " + klongTime + ", " + time 
                            + ", index=" + i);
                }
                time = klongTime;
            }
        }
    }

    private void checkLastTimeIndex() throws AssertionError {
        int index = this.lastTimeIndex;
        if (index != -1) {
            long klong = klongs[index];
            Assert.assertEquals(Klong.TYPE_TIME, Klong.getType(klong));
            long time = Klong.getTime(klong);
            if (time < 0) {
                throw new AssertionError("Bad time, " + time);
            }
        }
    }

    private void checkSizes() throws AssertionError {
        short sz = this.size;
        
        if (klongs.length < sz) {
            throw new AssertionError("klongs.length too small, " + klongs.length + ", sz=" + sz);
        }
        
        if (pointers.length < sz) {
            throw new AssertionError("pointers.length too small, " + pointers.length + ", sz=" + sz);
        }
        
        if (pos.length < sz) {
            throw new AssertionError("pos.length too small, " + pos.length + ", sz=" + sz);
        }
    }
    
    /**
     * Validates this node. Stream pointers for time > startupTime are 
     * allowed to be Spos.NULL (-1).
     * 
     * @throws Invalid
     */
    public void validateStreamNode(long startupTime) {
        short sz = this.size;
        
        if (sz < 1) {
            throw new Invalid("Key node with size " + sz + ", " + toString() + ".");
        }
        
        try {
            checkSizes();
            checkLastTimeIndex();
            checkIncreasingTime();
        } catch (AssertionError e) {
            throw new Invalid(e.getMessage());
        }
        
        long klongTime = 0;
        
        for (int i = 0; i < sz; i++) {
            long klong = klongs[i];
            long type = Klong.getType(klong);
            
            if (type == Klong.TYPE_TIME) {
                klongTime = Klong.getTime(klong);
            } else if (type == Klong.TYPE_KEY) {
                if (pointers[i] == null) {
                    // if stream pointer...
                    long spos = pos[i];
                    
                    if (klongTime > startupTime) {
                        if (!Spos.isValidOrNull(spos)) {
                            throw new Invalid("Bad spos of pointer " + i + " of node " 
                                    + this + ".");
                        }
                    } else {
                        if (!Spos.isValid(spos)) {
                            throw new Invalid("Bad spos of pointer " + i + " of node " + this.print() + ". Startup time: " + startupTime);
                        }
                    }
                } else {
                    // memory pointer, no further validation
                }
            }
        }
    }
    
    /**
     * Returns null if check is OK; otherwise a String with an error message
     * is returned.
     */
    public String checkWithMessage() {
        String result = null;
        try {
            check();
        } catch (AssertionError e) {
            result = e.toString();
        }
        return result;
    }

    private KlongIter createKlongIter() {
        return new KlongIter() {
            int offset = 0;
            int size = KeyNode.this.size;

            public boolean hasNext() {
                return offset < size;
            }

            public long next() {
                long klong = KeyNode.this.klongs[offset];
                offset++;
                return klong;
            }
            
        };
    }

    /**
     * Iterates the node to create a delete bitmap klong to add to the node to delete a klong
     * with the specified 'compareValue'.
     * If no klong needs to be added, 0 is returned. In that case, the delete is a noop - 
     * deleting of non-existing data.
     */
    public long getDeleteBitmap(final long compareValue) {
        short sz;
        long[] klongs;
        int index = 0;
        long klong;
        int klongType;
        long deleteBitmap;
        long newDeleteBitmap = 0;
        
        sz = this.size;
        klongs = this.klongs;
        deleteBitmap = this.getLastDeleteBitmap(sz);
        
        for (index = 0; index < sz; index++) {
            if (Klong.isDeleted(deleteBitmap, index)) {
                continue;
            }
            
            klong = klongs[index];
            klongType = Klong.getIntType(klong);
            
            switch (klongType) {
            case Klong.INT_TYPE_TIME:
            case Klong.INT_TYPE_DELETE_BITMAP:
                // Empty - nothing to do.
                break;
            case Klong.INT_TYPE_KEY:
                if (compareValue == Klong.getCompareValue(klong)) {
                    if (newDeleteBitmap == 0) {
                        newDeleteBitmap = Klong.delete(deleteBitmap, index);
                    } else {
                        newDeleteBitmap = Klong.delete(newDeleteBitmap, index);
                    }
                }
                break;                
            default:
                assert false : "Bad klong type, " + klongType;
                break;
            }
        }
        
        return newDeleteBitmap;
    }
    
    /**
     * Returns the last delete bitmap klong.
     * 
     * @param sz Size of this.klongs according to caller.
     */
    long getLastDeleteBitmap(short sz) {
        long del = Klong.createDelete();
        int s;
        long[] klongs;
        int index = 0;
        long klong;
        int klongType;
        
        s = this.size;
        klongs = this.klongs;
        
        for (index = 0; index < s; index++) {
            klong = klongs[index];
            klongType = Klong.getIntType(klong);
            
            switch (klongType) {
            case Klong.INT_TYPE_TIME:
            case Klong.INT_TYPE_KEY:
                // Empty - nothing to do.
                break;
            case Klong.INT_TYPE_DELETE_BITMAP:
                del = klong;
                break;
            default:
                assert false : "Bad klong type, " + klongType;
                break;
            }
        }
        
        return del;
    }
    
    /**
     * Iterates the node up until size sz and returns the last delete bitmap klong with a time 
     * LTE 'time'.
     * If no such klong is found, a delete bitmap klong with no delete bits set is returned.
     */
    public final long getDeleteBitmapAtTime(long time, int sz) {
        long del = Klong.DELETE_NONE_BITMAP;
        final long[] klongs = this.klongs;
        long klong;
        
        Loop: for (int index = 0; index < sz; index++) {
            klong = klongs[index];
            
            // Not inlined: switch (Klong.getIntType(klong)) {
            switch ((int) ((klong & 0xc000000000000000L) >>> 62)) {
            case Klong.INT_TYPE_TIME:
                // Not inlined: if (Klong.getTime(klong)) {
                if ((klong & 0x00ffffffffffffffL) > time) {
                    break Loop;
                }
                break;
            case Klong.INT_TYPE_DELETE_BITMAP:
                del = klong;
                break;
            case Klong.INT_TYPE_KEY:
                // Empty
                break;
            default:
                assert false : "Bad klong type, " + Klong.getIntType(klong);
                break;
            }
        }
        
        return del;
    }

    /**
     * Returns the first klong time. If there are no TIME klongs, -1 is returned.
     */
    public long getFirstTime() {
        long time = -1;
        short sz = this.size;
        
        for (int i = 0; i < sz; i++) {
            long klong = klongs[i];
            if (Klong.getType(klong) == Klong.TYPE_TIME) {
                time = Klong.getTime(klong);
                break;
            }
        }
        
        return time;
    }

    /**
     * Returns the maximum lookup time for which the pointer at the given
     * pointer index is valid. The klong may be deleted or overwritten later
     * in the key node klongs.
     */
    public long getMaxValidTime(int pointerIndex) {
        long klongAtIndex = this.klongs[pointerIndex];
        assert Klong.isKey(klongAtIndex) 
                : "klong not of KEY type as expected, " + Klong.toString(klongAtIndex);
        long time = 0;
        long maxValidTime = Long.MAX_VALUE;
        
        int sz = this.size;
        A: for (int i = pointerIndex; i < sz; i++) {
            long klong = klongs[i];
            
            switch (Klong.getIntType(klong)) {
            case Klong.INT_TYPE_TIME:
                time = Klong.getTime(klong);
                break;
            case Klong.INT_TYPE_KEY:
                if (klong == klongAtIndex && time != 0) {
                    maxValidTime = time - 1;
                    break A;
                }
                break;
            case Klong.INT_TYPE_DELETE_BITMAP:
                if (Klong.isDeleted(klong, pointerIndex) && time != 0) {
                    maxValidTime = time - 1;
                    break A;
                }
                break;
            }
        }
        
        return maxValidTime;
    }
    
    /**
     * Thrown to indicate that a KeyNode is not in a valid state.
     */
    public static class Invalid extends RuntimeException {
        private static final long serialVersionUID = 1L;
        
        public Invalid(String message) {
            super(message);
        }
    }
}
