# bergdb 024-18: option 2, compaction at the write, as a patch on Dag (main or 024-21-merges).
# Run in java/src/bergdb. Exact string replacement, keeps trailing whitespace elsewhere.
import sys
p = 'dag/Dag.java'
s = open(p).read()
def rep(old, new, first=False):
    global s
    if first and s.count(old) >= 1:
        s = s.replace(old, new, 1)
        return
    if s.count(old) != 1:
        sys.exit("anchor found %d times: %r" % (s.count(old), old[:70]))
    s = s.replace(old, new)

rep("""    /** Counts for tests and measurements; written by the writer only. */
""", """    // ======== Option 2 of bergdb 024-18: compaction at the write ========
    //
    // A write to a key node that holds THETA or more dead KEY klongs (deleted by its last bitmap,
    // or shadowed by a later KEY klong of the same compare value) handles the node as full: rule O
    // replaces it by its last version with the write applied, a time split, or a space split if
    // the last version and the write do not fit in the node. So no node holds more than THETA
    // dead klongs after a write, and reclaim's rewrites, which are writes, compact the cold
    // leaves they visit. THETA 0: off, as before. For measurements: -Dbergdb.theta=T; to land,
    // a rule of the record format as a function of the node size (024-18, section 4).
    
    /** Option 2's threshold; 0: off. */
    public static final int THETA = Integer.getInteger("bergdb.theta", 0);
    
    /** Compactions made by option 2 (not counting rule O's own splits); writer only. */
    public static volatile long statCompactions;
    
    /** Set by a write that replaces a node for option 2 only, read by handleFullNode. */
    private boolean compacting = false;
    
    /** The dead KEY klongs of 'node': deleted by its last bitmap, or shadowed. */
    static int deadCount(KeyNode node) {
        final int sz = node.size;
        final long del = node.getDeleteBitmapAtTime(Klong.MAX_TIME, sz);
        int dead = 0;
        for (int i = 0; i < sz; i++) {
            final long k = node.klongs[i];
            if (!Klong.isKey(k)) continue;
            if (Klong.isDeleted(del, i)) {
                dead++;
                continue;
            }
            final long cv = Klong.getCompareValue(k);
            for (int j = i + 1; j < sz; j++) {
                final long k2 = node.klongs[j];
                if (Klong.isKey(k2) && Klong.getCompareValue(k2) == cv) {
                    dead++;
                    break;
                }
            }
        }
        return dead;
    }
    
    /** Option 2: whether a write to 'node' replaces it. */
    private static boolean compact(KeyNode node) {
        return THETA > 0 && deadCount(node) >= THETA;
    }
    
    /** Counts for tests and measurements; written by the writer only. */
""", first=True)

# a put of a value
rep("""            if (node.size + 1 < this.maxNodeSize) {
                node.addKlong(pd.tt, Klong.compareValueToKeyKlong(compareValue),
                        valueNode, pd.accessData);""", """            if (node.size + 1 < this.maxNodeSize && !compact(node)) {
                node.addKlong(pd.tt, Klong.compareValueToKeyKlong(compareValue),
                        valueNode, pd.accessData);""")
# a put of a segment root
rep("""            if (current.size + 1 < this.maxNodeSize) {""",
    """            if (current.size + 1 < this.maxNodeSize && !compact(current)) {""")
# a delete's bitmap
rep("""                if (node.size + 1 < this.maxNodeSize) {
                    node.addDeleteKlong(tTime, union);
                    pd.nodeChangeListener.keyNodeChanged(node);
                } else {                    
                    KeyNode last = node.lastVersionGivenDel(sz, tTime, union);
""", """                if (node.size + 1 < this.maxNodeSize && !compact(node)) {
                    node.addDeleteKlong(tTime, union);
                    pd.nodeChangeListener.keyNodeChanged(node);
                } else {                    
                    KeyNode last = node.lastVersionGivenDel(sz, tTime, union);
                    compacting = node.size + 1 < this.maxNodeSize;
""")
# every other klong (a child's klong in its parent)
rep("""        final boolean isFull = node.size + toAppend.length + 1 > this.maxNodeSize;
""", """        final boolean sizeFull = node.size + toAppend.length + 1 > this.maxNodeSize;
        final boolean isFull = sizeFull || compact(node);
""")
rep("""            KeyNode last = node.lastVersion(pd.tt);
            
            assert last.assertOk(maxNodeSize);
            handleFullNode(node, depth, toAppend, pd.tt, last, pd);""",
"""            KeyNode last = node.lastVersion(pd.tt);
            
            assert last.assertOk(maxNodeSize);
            compacting = !sizeFull;
            handleFullNode(node, depth, toAppend, pd.tt, last, pd);""")
# handleFullNode: a compaction is a time split when the last version and the write fit
OLD_MAIN = """        final boolean newInTrans = node.getFirstTime() == tTime;
        
        if (last.size > this.maxNodeSize / 2) {"""
NEW_MAIN = """        final boolean newInTrans = node.getFirstTime() == tTime;
        final boolean byCompaction = compacting;
        compacting = false;
        if (byCompaction) statCompactions++;
        
        if (last.size > this.maxNodeSize / 2
                && !(byCompaction && last.size + toInsert.length + 1 < this.maxNodeSize)) {"""
OLD_MG = """        final boolean newInTrans = node.getFirstTime() == tTime;
        pd.fullNodes++;
        
        if (last.size > splitHalf()) {"""
NEW_MG = """        final boolean newInTrans = node.getFirstTime() == tTime;
        pd.fullNodes++;
        final boolean byCompaction = compacting;
        compacting = false;
        if (byCompaction) statCompactions++;
        
        if (last.size > splitHalf()
                && !(byCompaction && last.size + toInsert.length + 1 < this.maxNodeSize)) {"""
OLD_021 = """        final boolean newInTrans = node.getFirstTime() == tTime;
        
        pd.fullNodes++;                 // the key access path may be stale now (merges)
        
        if (last.size > splitAbove(this.maxNodeSize)) {"""
NEW_021 = """        final boolean newInTrans = node.getFirstTime() == tTime;
        
        pd.fullNodes++;                 // the key access path may be stale now (merges)
        final boolean byCompaction = compacting;
        compacting = false;
        if (byCompaction) statCompactions++;
        
        if (last.size > splitAbove(this.maxNodeSize)
                && !(byCompaction && last.size + toInsert.length + 1 < this.maxNodeSize)) {"""
if s.count(OLD_021) == 1:
    s = s.replace(OLD_021, NEW_021)
elif s.count(OLD_MAIN) == 1:
    s = s.replace(OLD_MAIN, NEW_MAIN)
elif s.count(OLD_MG) == 1:
    s = s.replace(OLD_MG, NEW_MG)
else:
    sys.exit("handleFullNode's anchor not found: apply by hand")
open(p, 'w').write(s)
print("patched Dag")
