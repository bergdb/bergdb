# 024-14: thresholds m, h, c settable for a measuring run (exact replacements, trailing whitespace kept)
import sys
p = '/Users/f/fl/bench/2026-11-11/thr/clone/java/src/bergdb/dag/Dag.java'
s = open(p).read()
def rep(old, new):
    global s
    n = s.count(old)
    assert n == 1, (n, old)
    s = s.replace(old, new)

rep("""    /** A node of fewer live compare values than this, not a root, is merged (B / 4). */
    private int mergeBelow() {
        return Math.max(2, maxNodeSize / 4);
    }
    
    /** A merge makes one node of at most this many live klongs, else two (B / 2). */
    private int mergeMax() {
        return maxNodeSize / 2;
    }
""", """    /**
     * The thresholds of a measuring build (bergdb 024-14; 024-11, section 5.1): m, the least
     * live klongs of a node that is not a root (mergeBelow); h, the most klongs of a last
     * version that a time split keeps (splitHalf; more: a space split); c, the most live
     * klongs that a merge puts in one node (mergeMax). Set for a run by "-Dbergdb.thr=m,h,c",
     * given for B = 30 and scaled to another node size B as v * B / 30, m at least 2; without
     * it P5's: max(2, B / 4), B / 2, B / 2. Not for production: a database must be rerun with
     * the thresholds it was written with.
     */
    static final int[] THR = parseThresholds(System.getProperty("bergdb.thr"));
    
    /** Splits counted in handleFullNode, for measurements (bergdb 024-14); the writer's. */
    public static volatile long statTimeSplits, statSpaceSplits;
    
    private static int[] parseThresholds(String v) {
        if (v == null || v.isEmpty()) {
            return null;
        }
        String[] a = v.split(",");
        if (a.length != 3) {
            throw new IllegalArgumentException("bergdb.thr: m,h,c expected, got " + v);
        }
        return new int[] {Integer.parseInt(a[0].trim()), Integer.parseInt(a[1].trim()),
                Integer.parseInt(a[2].trim())};
    }
    
    /** The thresholds {m, h, c} for node size b (see THR); checks that they keep V1. */
    public static int[] thresholds(int b) {
        final int m, h, c;
        if (THR == null) {
            m = Math.max(2, b / 4);
            h = b / 2;
            c = b / 2;
        } else {
            m = Math.max(2, THR[0] * b / 30);
            h = THR[1] * b / 30;
            c = THR[2] * b / 30;
            // a space split's halves and a redistribution's halves hold m or more; one merged
            // node holds 2m - 1 or more, and fits; a time split leaves room for its klongs
            if (h / 2 < m || (c + 1) / 2 < m || 2 * m - 1 > c || h > b - 2 || c > b - 2) {
                throw new IllegalArgumentException("bergdb.thr " + THR[0] + "," + THR[1] + ","
                        + THR[2] + " gives m=" + m + " h=" + h + " c=" + c + " for B=" + b
                        + ": not a valid set");
            }
        }
        return new int[] {m, h, c};
    }
    
    /** A node of fewer live compare values than this, not a root, is merged (m). */
    private int mergeBelow() {
        return THR == null ? Math.max(2, maxNodeSize / 4) : thresholds(maxNodeSize)[0];
    }
    
    /** A last version of more klongs than this is split in two, else replaced (h). */
    private int splitHalf() {
        return THR == null ? maxNodeSize / 2 : thresholds(maxNodeSize)[1];
    }
    
    /** A merge makes one node of at most this many live klongs, else two (c). */
    private int mergeMax() {
        return THR == null ? maxNodeSize / 2 : thresholds(maxNodeSize)[2];
    }
""")

rep("""        if (last.size > this.maxNodeSize / 2) {
            if (newInTrans) {""", """        if (last.size > splitHalf()) {
            statSpaceSplits++;
            if (newInTrans) {""")
rep("""        } else {
            if (newInTrans) {
                timeSplitInPlace(tTime, node, last, toInsert, pd);""", """        } else {
            statTimeSplits++;
            if (newInTrans) {
                timeSplitInPlace(tTime, node, last, toInsert, pd);""")

rep("""        final long m = Math.max(2, maxNodeSize / 4);
        final long perLevel = deletes * (len + 2);     // two levels more for new roots
        final long merges = m >= 3 ? Math.min""", """        final long m = mergeBelow();
        final long perLevel = deletes * (len + 2);     // two levels more for new roots
        // the sharper count is P5's argument for its thresholds only (bergdb 024-14)
        final long merges = THR == null && m >= 3 ? Math.min""")
old_q = "        final long q = Math.max(2, maxNodeSize / 2 - 3);\n"
assert s.count(old_q) == 2
s = s.replace(old_q, "        final long q = Math.max(2, Math.min(maxNodeSize / 2,\n                Math.min(maxNodeSize - splitHalf(), maxNodeSize - mergeMax())) - 3);\n")
open(p, 'w').write(s)
print("ok")
