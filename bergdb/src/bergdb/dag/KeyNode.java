package bergdb.dag;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;

import bergdb.common.Bug;
import bergdb.common.Bytes;
import bergdb.common.Util;
import bergdb.nanotest.Assert;
import bergdb.storage.StreamFormatException;

/**
 * <p>A key node has an array of "klongs" and corresponding INode references.</p>
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
 * @author Frans Lundberg
 */
public class KeyNode implements INode {
    public long spos;
        // The stream position of the node when it was last written to the stream.
        // Synch note: see get/set methods. Synched by read/write to volatile field this.size.
    public long id;            
        // id is used for debug purpose. It is the first spos of the node.
        // Synch note: synch issues not properly considered since it could be removed.
    private short lastTimeIndex = -1;
        // -1 or array index to the last time.
        // Synch note: this field should only be accessed by a writer. Access by a reader is not
        // allowed!
    private final boolean isSegmentLeaf;
        // Synch note: final, so we are fine :-)
    public boolean isInTransNodes = false;
        // Synch note: no need for volatile or something since all access is from threads 
        // holding DB.writeLock.
    
    public volatile short size;
        // Size of klong array actually used. 
        // Synch note: Used for synch action between writer and readers. Handles synch for 
        // the arrays too (klongs, pointers, pos).
    public long[] klongs;
        // Synch note: Writes to "klongs" and its elements published by a write to this.size.
        // Readers should first read this.size, before accessing klongs or elements in klongs.
    
    public INode[] pointers;           
        // Memory pointers to value nodes or other key nodes. Elements can be null.
        // Synch note: access protected by "this" lock and used atomically with "pos".
    public long[] pos;
        // spos for a stream pointer, access data for a memory pointer (see AccessData).
        // Synch note: access protected by "this" lock and used atomically with "pointers".

    private static final int[] arraySizes 
            = new int[]{2, 8-2, 16-2, 32-2, 64-2, 128-2};
        // Sizes for klong array.
    
    private static final long[] EMPTY_LONG_ARRAY = new long[0];
    private static final INode[] EMPTY_INODE_ARRAY = new INode[0];
    
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
        this.size = 0;    
            // Synch action to make constructor writes are visible to others threads that reads the
            // field this.size.
    }
    
    public final byte getType() {
        return INode.TYPE_KEY_NODE;
    }
    
    public final boolean isTopOrKeyNode() {
        return true;
    }
    
    // 130129 Frans: could not measure performance improvement by implementing hashCode.    
    //public final int hashCode() {
    //    return (int) this.id;
    //}
    
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
    
    //public final boolean isDirty() {
    //    return isDirty;
    //}
    
    //public final void setIsDirty(boolean isDirty) {
    //    this.isDirty = isDirty;
    //}
    
    public final long getKlong(int index) {
        return klongs[index];
    }
    
    public final int getPointerCount() {
        return size;
    }
    
    public final void getPointer(int index, Pointer pointer) {
        pointer.node = pointers[index];
        pointer.pos = pos[index];
    }
    
    public final INode getPointerNode(int index) {
        return pointers[index];
    }
    
    public final long getPointerPos(int index) {
        return pos[index];
    }
    
    public final void setPointer(int index, INode node, long spos) {
        // Besides DB.start() only called from DB.evictInner() and DB.followPointer().
        
        pointers[index] = node;
        pos[index] = spos;
    }
    
    public final void setPointerAccessData(int pointerIndex, long accessData) {
        // 'pos' is used for accessData when the pointer is a memory pointer and as a stream pos
        // when the pointer is a stream pointer.
        // Only called from DB.followPointer().
        
        pos[pointerIndex] = accessData;
    }
    
    public final long getPointerAccessData(int pointerIndex) {
        return pos[pointerIndex];
    }
    
    public void accept(NodeVisitor visitor) {
        visitor.visit(this);
    }
    
    private static final String classname = KeyNode.class.getName();
    
    public String toString() {
        String result = super.toString();
        if (result.startsWith(classname)) {
            String sub = result.substring(classname.length());
            if (sub.length() > 5) {
                sub = sub.substring(sub.length() - 2);
            }
            result = "K@" + sub;
        }
        
        String midPart = (id == -1 && spos == -1) ? "" : " " + id + ":" + spos + "";
        
        result = result + midPart;
        result = isSegmentLeaf ? result + " L" : result;
        //result = isDirty ? result + " D" : result;
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
        //
        // Should we have two searchEQ method, one for value pointers, one for key node pointers?
        // I suppose the caller does know what he is looking for.
        //
        // Perf note 2012-06: Inlining did not improve performance significantly.
        //
        
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
            if ((deleteBitmap & Klong.deleteBits[index]) != 0) {
                continue;
            }
            
            klong = klongs[index];
            
            // Not inlinded: klongType = Klong.getIntType(klong);
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
                    kwi.node = this.pointers[index];      // Warning, unsynched access to pointer.
                    kwi.pos = this.pos[index];
                }
                break;
            case Klong.INT_TYPE_DELETE_BITMAP:
                deleteBitmap = klong;
                // Not inlined: if (kwi.klong != Klong.NULL && Klong.isDeleted(deleteBitmap, kwi.pointerIndex)) {
                if (kwi.klong != Klong.NULL && (deleteBitmap & Klong.deleteBits[kwi.pointerIndex]) != 0) {
                    kwi.klong = Klong.NULL;
                }
                break;
            default:
                assert false : "Bad klong type, " + klongType;
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
            if ((del & Klong.deleteBits[i]) != 0) {
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
            }
        }
        
        if (bestCompareValue != -1) {
            kwi.klong = klongs[bestPointerIndex];
            kwi.pointerIndex = bestPointerIndex;
            kwi.klongTime = bestKlongTime;
            kwi.pos = this.pos[bestPointerIndex];     // Warning, unsynched access to pointer.
            kwi.node = this.pointers[bestPointerIndex];
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
            if ((del & Klong.deleteBits[i]) != 0) {
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
            }
        }
        
        if (bestCompareValue != -1) {
            kwi.klong = klongs[bestPointerIndex];
            kwi.pos = this.pos[bestPointerIndex];
            kwi.node = this.pointers[bestPointerIndex];
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
            if ((del & Klong.deleteBits[i]) != 0) {
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
            }
        }
        
        if (bestCompareValue != -1) {
            kwi.klong = klongs[bestPointerIndex];
            kwi.pos = this.pos[bestPointerIndex];
            kwi.node = this.pointers[bestPointerIndex];
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
            if ((del & Klong.deleteBits[i]) != 0) {
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
            }
        }
        
        if (bestCompareValue != -1) {
            kwi.klong = klongs[bestPointerIndex];
            kwi.pos = this.pos[bestPointerIndex];
            kwi.node = this.pointers[bestPointerIndex];
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
            if ((del & Klong.deleteBits[i]) != 0) {
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
            }
        }
        
        if (bestCompareValue != -1) {
            kwi.klong = klongs[bestPointerIndex];
            kwi.pos = this.pos[bestPointerIndex];
            kwi.node = this.pointers[bestPointerIndex];
            kwi.pointerIndex = bestPointerIndex;
            kwi.klongTime = bestKlongTime;
        }
    }
    
    /**
     * Adds a klong with a pointer and accessData to the end of the key node.
     * If needed, a time klong is added before 'klong'.
     */
    public void addKlong(long time, long klong, INode pointer, long accessData) {
        short sz;
        
        sz = this.size;             // Synch action, makes previous writes visible.
        
        assert lastTimeIndex == -1 || time >= klongs[lastTimeIndex];
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
        this.pos[newSize] = accessData;
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
    public boolean replaceKlong(long time, long klong1, INode pointer, long accessData) {
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
                    this.pos[index] = accessData;
                    result = true;
                    break A;
                }
                break;
            case Klong.INT_TYPE_DELETE:
            case Klong.INT_TYPE_DELETE_BITMAP:
                throw new IllegalStateException("This method is cannot be used for "
                        + "KeyNode with delete klongs.");
            }
        }
        return result;
    }
    
    /**
     * Write access required.
     * Note, writes not synched. The caller should make the writes of this method available to 
     * other threads by writing to this.size.
     */
    private void ensureCapacity(int neededSize) {
        int sz = this.size;
        
        assert sz <= klongs.length;
        
        if (neededSize > klongs.length) {
            int newSize = -1;
            final int arraySizesLength = KeyNode.arraySizes.length;
            for (int i = 0; i < arraySizesLength; i++) {
                int arraySize = KeyNode.arraySizes[i];
                if (arraySize >= neededSize) {
                    newSize = arraySize;
                    break;
                }
            }
            
            if (newSize == -1) {
                newSize = neededSize + 10;
            }
            
            long[] klongs = new long[newSize];
            INode[] pointers = new INode[newSize];
            long[] pos = new long[newSize];
            
            System.arraycopy(this.klongs, 0, klongs, 0, sz);
            System.arraycopy(this.pointers, 0, pointers, 0, sz);
            System.arraycopy(this.pos, 0, pos, 0, sz);
            
            this.klongs = klongs;
            this.pointers = pointers;
            this.pos = pos;
        }
    }
    
    /**
     * Adds a klong and its pointer to the end of the arrays.
     * No checking is used. Write access required.
     */
    private void addToEnd(long klongToAdd, INode pointerToAdd, long posToAdd) {
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
     * Returns a new key node that is the last version of this node. The returned node has a 
     * klong array that is sorted in strictly increasing compare value order.
     * 
     * @param time The time to get the last version.
     */
    public final KeyNode lastVersion(long time) {
        //
        // A simple brute-force method that scales with n^2, n = this.size.
        // Could still be faster than sorting first because of limited size.
        // Write access is *not* required.
        //
        
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
    public KeyNode lastVersionGivenDel(final short sz, long time, long del) {
        //
        // A simple brute-force method that scales with n^2, n = this.size.
        // Could still be faster than sorting first because of limited size.
        // Write access is *not* required.
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
            INode pointerToAdd = null;
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
    private void addToSorted(long klongToAdd, INode pointerToAdd, long posToAdd) {
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
        assert last.checkWithMessage() == null;
        
        KeyNode insertTo = first;
        if (insert.length > 0 && Klong.getCompareValue(insert[0].klong) >= Klong.getCompareValue(secondKlong)) {
            insertTo = second;
        }
        
        for (int i = 0; i < insert.length; i++) {
            KlongWithPointer kwi = insert[i];
            insertTo.addToEnd(kwi.klong, kwi.node, kwi.pos);
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

    public final int getByteSize() {
        return 32 + size * 16;
    }
    
    /**
     * Writes the node to a long buffer.
     */
    public int toLongs(long[] buffer, final int firstOffset, long prevPos) {
        int sz = this.size;
        int byteSize = getByteSize();
        int offset = firstOffset;
        
        buffer[offset++] = ((long)byteSize) | (((long)INode.TYPE_KEY_NODE) << (4*8)) | (1L << (5*8));
            // 2 bytes available for checksum
        buffer[offset++] = prevPos;
        buffer[offset++] = ((long) (isSegmentLeaf ? 1 : 0)) | sz << (1*8);
            // 5 zero bytes available...
        buffer[offset++] = id;
        
        System.arraycopy(klongs, 0, buffer, offset, sz);
        offset += sz;
        
        for (int i = 0; i < sz; i++) {
            long spos = pointers[i] == null ? pos[i] : pointers[i].getSpos();
            buffer[offset++] = spos;
        }
        
        // Checksum, XOR of all bytes.
        
        long checksum = 0;
        for (int i = firstOffset; i < offset; i++) {
            checksum ^= buffer[i];
        }
        
        checksum = 0x000000ff &
               ((checksum >>> 0)  ^ (checksum >>> 8)  ^ (checksum >>> 16) ^ (checksum >>> 24)
              ^ (checksum >>> 32) ^ (checksum >>> 40) ^ (checksum >>> 48) ^ (checksum >>> 56));
        checksum = checksum == 0 ? 1 : checksum;
        buffer[firstOffset] = buffer[firstOffset] | (checksum << (6*8));
        
        assert (offset - firstOffset) * 8 == byteSize;
        assert byteSize % 8 == 0;
        return byteSize / 8;
    }
    
    /**
     * Gets the previous spos directly from the byte buffer.
     * Note, this method must be updated if toBytes() is changed.
     */
    public static long prevPosFromBytes(byte[] buffer, int offset) {
        // This is a hack we would like to avoid.
        long result = Bytes.bytesToLongLE(buffer, offset + 8);
        if (result != Spos.NULL && result < 0) {
            throw new StreamFormatException("Bad KeyNode, prevPos is illegal: " + result + ".");
        }
        return result;
    }
    
    /**
     * Creates a Node from bytes.
     * 
     * @throws StreamFormatException if buffer has badly formatted data.
     */
    public static KeyNode fromBytes(byte[] buffer, int offset, long spos) {
        offset += 4;          // Skip size.
        byte type = buffer[offset];
        offset += 1;
        if (type != INode.TYPE_KEY_NODE) {
            throw new Bug("Bad node type byte, " + ((int) type) 
                    + ", should have been checked already.");
        }
        
        byte version = buffer[offset];
        if (version != 1) {
            throw new StreamFormatException("Bad Node stream format version, expected 1, was " 
                    + ((int)version) + ".");
        }
        offset += 1;
        
        offset += 2;    // checksum bytes
        
        long prevPos = Bytes.bytesToLongLE(buffer, offset);
        if (prevPos != Spos.NULL && prevPos < 0) {
            throw new StreamFormatException("Bad KeyNode, prevPos is illegal: " + prevPos + ".");
        }
        offset += 8;
        
        if (!(buffer[offset] == 0 || buffer[offset] == 1)) {
            throw new StreamFormatException("Bad second byte, expected 0 or 1, was " 
                    + ((int) buffer[offset]) + ".");
        }
        boolean isSegmentLeaf = buffer[offset] == 1;
        offset += 1;
        
        int size = Bytes.bytesToShortLE(buffer, offset);
        if (size > Short.MAX_VALUE) {
            throw new StreamFormatException("Bad size: " + size + ", spos=" + spos + ".");
        }
        offset += 2;
        
        // 5 zero bytes
        offset += 5;
        
        long id = Bytes.bytesToLongLE(buffer, offset);
        offset += 8;
        
        if (size < 0) {
            throw new StreamFormatException("Bad Node size, " + size + ".");
        }
        
        long[] klongs = new long[size];
        long[] positions = new long[size];
        
        for (int i = 0; i < size; i++) {
            klongs[i] = Bytes.bytesToLongLE(buffer, offset);
            offset += 8;
        }
        
        for (int i = 0; i < size; i++) {
            positions[i] = Bytes.bytesToLongLE(buffer, offset);
            offset += 8;
        }
        
        KeyNode result = new KeyNode(isSegmentLeaf);
        result.spos = spos;
        result.id = id;
        
        for (int i = 0; i < size; i++) {
            result.addToEnd(klongs[i], null, positions[i]);
        }
        
        result.size = result.size;     // Synch action to publish writes.
        
        return result;
    }
    
    /**
     * Does not require write access.
     */
    public int getMemoryPointerCount() {
        int count = 0;
        int size = this.size;
        for (int i = 0; i < size; i++) {
            if (pointers[i] != null) count++;
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
        return Util.toString(bout.toByteArray());
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
        
        for (int i = 0; i < size; i++) {
            long klong = klongs[i];
            int type = Klong.getIntType(klong);
            
            out.print(indent + String.format("%02d", i) + ": ");
            
            switch (type) {
            case Klong.INT_TYPE_TIME:
                long arrayTime = Klong.getTime(klong);
                out.println("TIME: " + arrayTime);
                break;
                
            case Klong.INT_TYPE_KEY:
                String keyString = getKeyString(klong);
                out.print(String.format("%-15s", keyString));
                INode child = pointers[i];
                boolean isMem = child != null;
                
                if (isMem) {
                    if (printChildren && (child instanceof KeyNode)) {
                        KeyNode keyNodeChild = (KeyNode) child;
                        out.print(" ->\n");
                        keyNodeChild.printInternal(out, newIndent, depth + 1, true);
                        
                    } else {
                        out.println(" -> " + pointers[i].toString());
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
            }
        }
    }
    
    private static String getKeyString(long klong) {
        byte[] bytes = new byte[Klong.getLength(klong)];
        Klong.getKey(klong, bytes);
        return getKeyString(bytes);
    }
    
    /**
     * For printing, debug. Prints value of key klong.
     */
    public static String getKeyString(byte[] bytes) {
        // Assumes bytes created from ukey.
        
        String result;
        
        if (bytes == null) {
            result = "null";
        } else {
            if (Keys.isPrintableAscii(bytes)) {
                result = Keys.toString(bytes);
            } else {
                result = "#" + Util.toHexString(bytes);
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
            case Klong.INT_TYPE_DELETE:
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
     */
    public void check() {
        short sz = this.size;
        
        // Checks sizes
        
        if (klongs.length < sz) {
            throw new AssertionError("klongs.length too small, " + klongs.length + ", sz=" + sz);
        }
        
        if (pointers.length < sz) {
            throw new AssertionError("pointers.length too small, " + pointers.length + ", sz=" + sz);
        }
        
        if (pos.length < sz) {
            throw new AssertionError("pos.length too small, " + pos.length + ", sz=" + sz);
        }
        
        // Checks lastTimeIndex. Could return bad result in multi-threaded situations.
        
        int index = this.lastTimeIndex;
        if (index != -1) {
            long klong = klongs[index];
            Assert.assertEquals(Klong.TYPE_TIME, Klong.getType(klong));
            long time = Klong.getTime(klong);
            if (time < 0) {
                throw new AssertionError("Bad time, " + time);
            }
        }
        
        // Checks for increasing time klongs
        
        long time = Long.MIN_VALUE;
        for (int i = 0; i < sz; i++) {
            long klong = klongs[i];
            if (Klong.getType(klong) == Klong.TYPE_TIME) {
                long klongTime = Klong.getTime(klong);
                if (klongTime <= time) {
                    throw new AssertionError("Time not increasing, " + klongTime + ", " + time 
                            + ", index=" + i);
                }
            }
        }
        
        // Checks that memory pointers have accessData, not spos.
        
        for (int i = 0; i < sz; i++) {
            long klong = klongs[i];
            if (Klong.getType(klong) == Klong.TYPE_KEY) {
                if (pointers[i] != null) {
                    long accessData = pos[i];
                    
                    if (!AccessData.isValidOrNull(accessData)) {
                        throw new AssertionError("Bad access data (" + accessData 
                                + ") of pointer " + i + " of node " + this + ".");
                    }
                }
            }
        }
        
        // Checks that stream pointers have a valid spos.
        
        for (int i = 0; i < sz; i++) {
            long klong = klongs[i];
            if (Klong.getType(klong) == Klong.TYPE_KEY) {
                if (pointers[i] == null) {
                    long spos = pos[i];
                    
                    if (!Spos.isValidOrNull(spos)) {
                        throw new AssertionError("Bad spos of pointer " + i + " of node " 
                                + this + ".");
                    }
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
            
            public INode getNode() {
                return KeyNode.this.pointers[offset];
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
        long del = Klong.createDeleteBitmap();
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
        //
        // Perf note 2012-06: Tried loop unroll but did not improve performance on JVM 7.
        //
        
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
            }
        }
        
        return del;
    }
}

/*

130117 Frans. Made some fields private. Made isDirty volatile for synch reasons.
Checked the whole class for concurrency issues. There are no more synch issues that I know of.

*/