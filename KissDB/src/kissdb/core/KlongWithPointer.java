package kissdb.core;

/**
 * A klong with node pointer and possibly more related data.
 * Used internally in node search methods.
 * The pointer can be either a memory pointer (node != null, pos = accessData)
 * or a stream pointer (node == null, pos = stream position of the node).
 * 
 * @see KeyNode#searchEq(long, long, KlongWithPointer)
 * @see KeyNode#searchLte(long, long, KlongWithPointer)
 */
public class KlongWithPointer {
    long klong;         // The klong.
    int pointerIndex;   // Index of pointer.
    long klongTime;     // Time of the klong. Last TIME klong before the found klong. Added 120612.
    INode node;         // pointer (INode).
    long pos;           // pos - accessData or spos.
    
    public KlongWithPointer() {
        this.klong = Klong.NULL;
        this.pointerIndex = -1;
        this.klongTime = -1;
        this.node = null;
        this.pos = Spos.NULL;
    }
}
