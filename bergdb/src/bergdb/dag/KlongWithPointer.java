package bergdb.dag;

/**
 * A klong with node pointer and related data.
 * Used internally in node search methods.
 * The pointer can be either a memory pointer (node != null, pos = accessData)
 * or a stream pointer (node == null, pos = stream position of the node).
 * 
 * @see KeyNode#searchEq(long, long, KlongWithPointer)
 * @see KeyNode#searchLte(long, long, KlongWithPointer)
 */
public class KlongWithPointer {
    public long klong;         // The klong.
    public int pointerIndex;   // Index of pointer.
    public long klongTime;     // Time of the klong. Last TIME klong before the found klong. Added 120612.
    public Node node;         // pointer (Node).
    public long pos;           // pos - accessData or spos.
    
    public KlongWithPointer() {
        this.klong = Klong.NULL;
        this.pointerIndex = -1;
        this.klongTime = -1;
        this.node = null;
        this.pos = Spos.NULL;
    }
    
    /**
     * Returns true if the pointer of this object is not a memory pointer, 
     * nor a valid stream pointer.
     */
    public boolean isNullPointer() {
        return Pointer.isNull(node, pos);
    }
}
