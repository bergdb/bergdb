# bergdb 024-18: variant 3c of option 3, on top of patch-o2clean.py. Run in java/src/bergdb.
import sys
def patch(p, old, new):
    s = open(p).read()
    if s.count(old) != 1:
        sys.exit("anchor found %d times in %s: %r" % (s.count(old), p, old[:70]))
    open(p, 'w').write(s.replace(old, new))

patch('dag/Dag.java', '''    /** Option 2: whether a write to 'node' replaces it. */
    private static boolean compact(KeyNode node) {
        return THETA > 0 && deadCount(node) >= THETA;
    }
''', '''    // ======== Variant 3c of bergdb 024-18: reclaim's writes compact the cold nodes ========
    //
    // In a reclaim step's transaction (inReclaimStep, set by Reclaim.step), a write to a key node
    // whose last klong is older than the iteration's tStart (coldBefore), and that holds a dead
    // klong or would by this write, replaces the node by its last version with the write applied,
    // as rule O's time split; and a put of a key whose KEY klong in the node is of the
    // transaction's time (a node the step made or compacted) changes that klong in place. So a
    // cold node that a step writes is left as its last version, and a node changed in this
    // iteration (dirty, or made by an earlier step) is never replaced. For measurements:
    // -Dbergdb.reclaimCompact=1. To land, the step's record needs a flag so that a start's rerun
    // applies the same rule (024-18, sections 5.2 and 6.3).
    
    /** Variant 3c on. */
    public static final boolean RECLAIM_COMPACT = Integer.getInteger("bergdb.reclaimCompact", 0) == 1;
    
    /** Set by Reclaim.step around its transaction; the iteration's tStart. Writer only. */
    public static boolean inReclaimStep = false;
    public static long coldBefore = Long.MIN_VALUE;
    
    /** Option 2 and variant 3c: whether a write to 'node' replaces it. */
    private static boolean compact(KeyNode node) {
        if (RECLAIM_COMPACT && inReclaimStep) {
            return lastTime(node) < coldBefore;
        }
        return THETA > 0 && deadCount(node) >= THETA;
    }
    
    /** Variant 3c: the index of the key's KEY klong of time tt in 'node', or -1. */
    private static int klongOfTt(KeyNode node, long compareValue, long tt) {
        if (!(RECLAIM_COMPACT && inReclaimStep) || lastTime(node) != tt) return -1;
        for (int i = node.size - 1; i >= 0; i--) {
            final long k = node.klongs[i];
            if (!Klong.isKey(k)) return -1;
            if (Klong.getCompareValue(k) == compareValue) return i;
        }
        return -1;
    }
''')
patch('dag/Dag.java', '''            if (node.size + 1 < this.maxNodeSize && !compact(node)) {
                node.addKlong(pd.tt, Klong.compareValueToKeyKlong(compareValue),
                        valueNode, pd.accessData);''', '''            final int inPlace = klongOfTt(node, compareValue, pd.tt);
            if (inPlace >= 0) {
                node.repointKlong(inPlace, valueNode);
                pd.pointerCreatedListener.pointerCreated(node, inPlace, valueNode);
                pd.nodeChangeListener.keyNodeChanged(node);
            } else if (node.size + 1 < this.maxNodeSize && !compact(node)) {
                node.addKlong(pd.tt, Klong.compareValueToKeyKlong(compareValue),
                        valueNode, pd.accessData);''')
patch('core/Reclaim.java', '''        try {
            db.execute(t);
        } catch (RerunException e) {
            return;     // The same step is tried at a later transaction.
        }''', '''        try {
            bergdb.dag.Dag.inReclaimStep = true;
            bergdb.dag.Dag.coldBefore = it.tStart;
            db.execute(t);
        } catch (RerunException e) {
            return;     // The same step is tried at a later transaction.
        } finally {
            bergdb.dag.Dag.inReclaimStep = false;
        }''')
print("patched")
