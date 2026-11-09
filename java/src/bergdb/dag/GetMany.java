package bergdb.dag;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * Input/output to Db.getMany() and Dag.getMany(). Also data structures and algorithms to
 * support that method. A getMany() gives the KVs at the lookup time in key order, from
 * startKey, forward (increasing keys) or backward, while the stop condition goes on; the
 * stop condition gives the end (bergdb 020-27: this comment gave an interval (key1, key2]
 * of two keys that the class does not have).
 * 
 * <p>The defaults, as Db.newGetMany() gives it (bergdb 020-24-09, U9-8): lookupTime
 * Long.MAX_VALUE, the latest state; startKey null, from the first key; inclusive; forward;
 * stopCondition a DontStop, every KV to the end. The order is the unsigned order of the
 * keys' bytes (Db, "Keys and values"). A GetMany is for one call of getMany(), by one
 * thread: make a new one for each call. getMany() adds to result, which must be empty (with
 * -ea a GetMany whose result has KVs is refused with an AssertionError; without, the call
 * adds to them), and a stop condition keeps its own state, such as GetN's count.</p>
 * 
 * @see Dag#getMany(GetMany)
 * @author Frans Lundberg
 */
public class GetMany {
    
    // ---- Input ----
    
    /** 
     * Requested lookup time; Long.MAX_VALUE, the latest state, by default.
     */
    public long lookupTime;
    
    /** 
     * Forward, the first key gotten with getMany() is the smallest key GTE 'startKey' (GT
     * if not inclusive); backward, the largest key LTE it (LT if not inclusive).
     * Use 'null' to start at the first key, or backward at the last.
     */
    public long[] startKey;
    
    /**
     * By default, GetMany returns keys greater than or equal to (GTE) 'startKey', or
     * backward less than or equal to (LTE) it. To use strictly greater than (GT), or less
     * than (LT), set this field to false.
     */
    public boolean inclusive;
    
    /**
     * By default, GetMany iterates forward (increasing keys); set this field to false
     * to iterate backwards instead.
     */
    public boolean forward;
    
    /**
     * The condition for when to stop iterating; a DontStop, every KV to the end, by default.
     */
    public StopCondition stopCondition;
    
    // ---- Output ----
    
    /**
     * Actual time used for the lookup. Possibly different from the requested lookup time:
     * the time of the last transaction, if that was earlier (Db, "Threads").
     */
    public long actualLookupTime;
    
    /**
     * The resulting KVs, in the scan's order. A Kvt's time is the time of its key node entry,
     * not the time the value was written (Kvt.time; bergdb 021-19).
     */
    public final List<Kvt> result;
    
    /**
     * The GetData; used for get operations.
     */
    public final GetData gd;

    /**
     * The number of get operations run. Output.
     */
    public int getOpCount;
    
    /**
     * Creates a new instance; use Db.newGetMany() or Dag.newGetMany() instead when possible.
     */
    public GetMany() {
        result = new ArrayList<Kvt>();
        stopCondition = new DontStop();
        startKey = null;
        lookupTime = Long.MAX_VALUE;
        inclusive = true;
        forward = true;
        gd = new GetData();
        getOpCount = 0;
    }
    
    public void setBackward() {
        forward = false;
    }
    
    // ---- Inner classes / interfaces ----
    
    /**
     * Class that implements GetMany functionality. Keeps the node chain for the iteration.
     */
    public class Chain {
        // "Links" in the chain are node-compareValue pairs.
        // The links are stored in linkNodes, linkCompareValues and linkSize. More 
        // efficient then using ArrayList<Link> or something.
        
        KeyNode[] linkNodes;
        int linkSize;
        long[] linkCompareValues;
        long[] keySegments;
        int keySegmentSize;
        KlongWithPointer kwi;
        boolean first = true;
        boolean setupEqMatch = false;
        
        private final long[] chainStartKey;
        private final boolean chainForward;
        private final boolean chainInclusive;
        
        public Chain() {
            chainStartKey = GetMany.this.startKey;
            chainForward = GetMany.this.forward;
            chainInclusive = GetMany.this.inclusive;
            
            linkNodes = new KeyNode[4];
            linkCompareValues = new long[4];
            linkSize = 0;
            keySegments = new long[4];
            keySegmentSize = 0;
            kwi = new KlongWithPointer();
        }
        
        private void addLink(KeyNode node, long compareValue) {
            if (linkSize == linkNodes.length) {
                assert linkNodes.length == linkCompareValues.length;
                
                KeyNode[] newLinkNodes = new KeyNode[linkNodes.length * 2];
                System.arraycopy(linkNodes, 0, newLinkNodes, 0, linkNodes.length);
                linkNodes = newLinkNodes;
                
                long[] newLinkCompareValues = new long[linkCompareValues.length * 2];
                System.arraycopy(linkCompareValues, 0, newLinkCompareValues, 0, 
                        linkCompareValues.length);
                linkCompareValues = newLinkCompareValues;
            }
            
            linkNodes[linkSize] = node;
            linkCompareValues[linkSize] = compareValue;
            linkSize++;
        }
        
        private int getLinkSize() {
            return linkSize;
        }
        
        private KeyNode getLinkNode(int index) {
            assert index < linkSize;
            return linkNodes[index];
        }
        
        private long getLinkCompareValue(int index) {
            assert index < linkSize;
            return linkCompareValues[index];
        }
        
        private void setLinkCompareValue(long compareValue) {
            linkCompareValues[linkSize - 1] = compareValue;
        }
        
        private void removeLink() {
            linkSize--;
        }
        
        private void addKeySegment(long segment) {
            assert keySegmentSize <= keySegments.length;
            if (keySegmentSize == keySegments.length) {
                long[] newKeySegments = new long[keySegments.length * 2];
                System.arraycopy(keySegments, 0, newKeySegments, 0, keySegmentSize);
                keySegments = newKeySegments;
            }
            
            keySegments[keySegmentSize] = segment;
            keySegmentSize++;
        }
        
        private void removeKeySegment() {
            keySegmentSize--;
        }
        
        /**
         * Sets up the chain to its initial state based on: g.startKey, g.inclusive, g.forward.
         * The initial state is at-or-before g.startKey, must be "at" if startKey equals an
         * existing key.
         */
        public void setup(KeyNode root) {
            long[] start = chainStartKey;
            final long lookupTime = actualLookupTime;
            final KlongWithPointer kwi = this.kwi;
            
            assert root != null;            
            
            if (start == null) {
                if (forward) {
                    start = new long[]{-1};   
                    // A special "key" that is less than any real DB key.
                } else {
                    start = new long[]{Long.MAX_VALUE};
                    // A special "key" that is greater than any real DB key.
                }
            }
            
            assert start.length > 0 : "startKey.length = " + start.length + ", not allowed";
            
            KeyNode node = root;
            final int segmentCount = start.length;
            int index = 0;
            boolean hasDiff = false; 
                // set to true when difference found between startKey and nearest db key.
            
            while (true) {
                long startKeySegment;
                
                if (index < segmentCount) {
                    startKeySegment = start[index];
                } else {
                    startKeySegment = forward ? Long.MAX_VALUE : -1;
                }
                
                if (hasDiff) {
                    if (forward) {
                        node.searchLt(lookupTime, Long.MAX_VALUE, kwi);
                    } else {
                        node.searchGt(lookupTime, -1, kwi);
                    }
                } else {
                    if (forward) {
                        node.searchLte(lookupTime, startKeySegment, kwi);
                    } else if (node.isSegmentLeaf()) {
                        node.searchGte(lookupTime, startKeySegment, kwi);
                    } else {
                        // 2026-10-13 (DbTesterGetMany.testInclusiveStartKeyWithDeepTree
                        // and testStartKeyRandom): above the leaf, the klong is the lower
                        // bound of its child, and the child that holds the start key is the
                        // last one at or before it, as for a forward scan. Searching for the
                        // first one at or after the start key took the next child, so a
                        // backward scan from a key in a tree of more than one node level began
                        // at a key above the start key.
                        node.searchLte(lookupTime, startKeySegment, kwi);
                    }
                }
                
                
                if (kwi.klong == Klong.NULL) {
                    // Backward above the leaf: the start key is before every key of the tree,
                    // so the position is before the first, not after the last.
                    boolean beforeFirst = !forward && !hasDiff && !node.isSegmentLeaf();
                    addLink(node, forward || beforeFirst ? -1 : Long.MAX_VALUE);
                    break;  // Done!
                } else {
                    addLink(node, Klong.getCompareValue(kwi.klong));
                }
                
                if (node.isSegmentLeaf() && Klong.getLength(kwi.klong) < Klong.MAX_SIZE) {
                    // No need to follow, we know it is a value node pointer. Done!
                    break;
                }
                
                Node next = gd.followPointer(node, kwi.pointerIndex);
                
                assert next instanceof KeyNode : "next=" + next;
                
                if (node.isSegmentLeaf()) {
                    long compareValue = Klong.getCompareValue(kwi.klong);
                    if (compareValue != startKeySegment) {
                        hasDiff = true;
                    }
                    addKeySegment(compareValue);
                    index++;
                }
                
                node = (KeyNode) next;
            }
            
            // -- Section below set setupEqMatch to true if setup results
            // in an exact match.
            
            assert linkSize > 0;
            
            setupEqMatch = eqMatch(start);
        }

        /**
         * Returns true if setup results in an exact match.
         *
         * <p>2026-10-13 (DbTesterGetMany.testInclusiveStartKeyWithDeepTree): this
         * compared the number of links, that is, nodes in the chain, with the number of
         * segments of the start key. The chain has one link for each node level of each
         * segment tree, so with a segment tree of more than one node (more than about 30
         * keys) an exact match was never found, and an inclusive start key was not returned.
         * The key segments passed so far (keySegments) and the last link are the key.</p>
         */
        private boolean eqMatch(long[] start) {
            if (keySegmentSize + 1 != start.length || linkSize == 0) {
                return false;
            }
            
            for (int i = 0; i < keySegmentSize; i++) {
                if (keySegments[i] != Klong.getCompareValue(start[i])) {
                    return false;
                }
            }
            
            return linkCompareValues[linkSize - 1]
                    == Klong.getCompareValue(start[start.length - 1]);
        }
        
        /**
         * Gets the next KV given the node chain. Updates the chain state accordingly.
         * 'null' is returned if there is no more KV.
         * The method handles iteration both forward and backward.
         */
        public Kvt next() {
            Kvt result = null;
            
            while (true) {   // dummy while just to be able to do "continue".
                int linkSize = getLinkSize();
                if (linkSize == 0) {
                    break;
                }
                
                KeyNode linkNode = getLinkNode(linkSize - 1);
                long linkCompareValue = getLinkCompareValue(linkSize - 1);
                
                if (first && chainInclusive && setupEqMatch) {
                    if (chainForward) {
                        linkNode.searchGte(actualLookupTime, linkCompareValue, kwi);
                    } else {
                        linkNode.searchLte(actualLookupTime, linkCompareValue, kwi);
                    }
                } else {
                    if (chainForward) {
                        linkNode.searchGt(actualLookupTime, linkCompareValue, kwi);
                    } else {
                        linkNode.searchLt(actualLookupTime, linkCompareValue, kwi);
                    }
                }
                first = false;
                
                if (kwi.klong == Klong.NULL) {
                    if (linkSize > 1) {
                        KeyNode parent = getLinkNode(linkSize - 2);
                        if (parent.isSegmentLeaf()) {
                            removeKeySegment();
                        }
                    }
                    
                    removeLink();
                    continue;
                }
                
                linkCompareValue = Klong.getCompareValue(kwi.klong);
                setLinkCompareValue(linkCompareValue);
                
                Node next = gd.followPointer(linkNode, kwi.pointerIndex);
                
                if (next instanceof ValueNode) {
                    // Found next KV, creates result.
                    ValueNode valueNode = (ValueNode) next;
                    result = new Kvt();
                    result.key = getKeySegments(Klong.getCompareValue(kwi.klong));
                    result.value = valueNode.getValue();   // Note, no copy.
                    result.time = kwi.klongTime;
                    result.spos = valueNode.getSpos();
                    break;  // Done!
                    
                } else {
                    assert next != null;
                    assert next instanceof KeyNode : next.toString();
                    
                    addLink((KeyNode) next, forward ? -1 : Long.MAX_VALUE);
                    if (linkNode.isSegmentLeaf()) {
                        addKeySegment(linkCompareValue);
                    }
                }
            }

            return result;
        }
        
        /**
         * Returns the current key as segments in a newly allocated long array.
         */
        long[] getKeySegments(long lastCompareValue) {
            // Note, since we allocate memory, we could efficiently return byte[] key instead.
            
            long[] result = new long[keySegmentSize + 1];
            System.arraycopy(keySegments, 0, result, 0, keySegmentSize);
            result[result.length - 1] = lastCompareValue;
            return result;
        }
    }
    
    /**
     * Implements a stop condition for Db.getMany().
     * Can be used as a combined stop condition and filter.
     */
    public static interface StopCondition {
        /** Add the KV and continue. */
        public static final int ADD = 1;
        
        /** Stop without adding the KV. */
        public static final int STOP = 2;
        
        /** Continue without adding the KV to the result. Could have been called FILTER. */
        public static final int CONTINUE = 3;
        
        /** Add KV and stop after that. */
        public static final int ADD_AND_STOP = 4;
        
        /**
         * Returns what to do with the KV. Four cases are possible.
         * 1. Add the KV to result and continue to next KV.
         * 2. Stop iterating, do not add the KV to the result.
         * 3. Continue to next KV without adding the current KV to the result.
         * 4. Add the Kv to the result and stop.
         * 
         * @return ADD/STOP/CONTINUE/ADD_AND_STOP.
         */
        public int handleKvt(Kvt kvt);
        
        /**
         * This is called to report that the end of database was reached.
         * This method will only be called once and handleKvt() will never be called after 
         * this method.
         */
        public void eod();
    }
    
    /**
     * A stop condition to never stop until end of database is reached. Useful for testing.
     */
    public static class DontStop implements StopCondition {
        public int handleKvt(Kvt kvt) {
            return ADD;
        }

        public void eod() {}
    }
    
    /**
     * A stop condition that stops at a specific endpoint key.
     */
    public static class Endpoint implements StopCondition {
        private boolean inclusive;
        private boolean backward;
        private long[] key;         // endpoint key segments
        private boolean eod;        // True if we got to "end of database"
        
        /**
         * Inclusive, forward direction end point.
         */
        public Endpoint(long[] key) {
            this(key, true, false);
        }
        
        public Endpoint(long[] key, boolean inclusive) {
            this(key, inclusive, false);
        }
        
        public Endpoint(long[] key, boolean inclusive, boolean backward) {
            assert key != null;
            this.inclusive = inclusive;
            this.key = key.clone();
            this.backward = backward;
        }
        
        public int handleKvt(Kvt kvt) {
            assert kvt != null;
            int compare = Keys.compareKeys(kvt.key, key);
            boolean stop;
            if (backward) {
                stop = inclusive ? compare < 0 : compare <= 0;
            } else {
                stop = inclusive ? compare > 0 : compare >= 0;
            }
            return stop ? STOP : ADD;
        }

        public void eod() {
            this.eod = true;
        }
    }
    
    /**
     * Gets at most N kvs.
     */
    public static class GetN implements StopCondition {
        private int count;
        private int maxCount;
        private boolean eod;
        
        public GetN(int maxCount) {
            assert maxCount >= 0;
            this.maxCount = maxCount;
            this.eod = false;
        }
        
        public int handleKvt(Kvt kvt) {
            // At most maxCount, none for 0 (bergdb 020-27): GetN(0) gave every KV, as the
            // count passed 0 before it was compared.
            if (count >= maxCount) {
                return STOP;
            }
            count++;
            return count == maxCount ? ADD_AND_STOP : ADD;
        }

        public void eod() {
            this.eod = true;
        }
    }
    
    /**
     * Gets at most one KV.
     */
    public static class GetOne extends GetN {
        public GetOne() {
            super(1);
        }
    }
    
    /**
     * True if 'key' starts with 'prefix': a strict prefix (Keys.isPrefix) or the key itself
     * (bergdb 021-18). A key has one segment array (Keys.toSegments), so equal keys have
     * equal arrays.
     */
    static boolean hasPrefix(long[] prefix, long[] key) {
        return Keys.isPrefix(prefix, key) || Arrays.equals(prefix, key);
    }
    
    /**
     * Adds the KVs whose keys start with a given prefix, the prefix's own key included, and
     * stops at the first KV whose key does not, which may be the scan's first. So a forward
     * scan from the prefix, inclusive (startKey the prefix, inclusive's default), gives every
     * key that starts with the prefix; exclusive, every one but the prefix's own. Until bergdb
     * 021-18 it stopped at the prefix's own key, as Keys.isPrefix() is a strict prefix, and
     * such a scan gave no KV when the prefix was a key.
     */
    public static class Prefix implements StopCondition {
        private long[] prefix;
        private boolean eod;
        
        public Prefix(long[] prefix) {
            assert prefix != null;
            this.prefix = prefix.clone();
        }
        
        public int handleKvt(Kvt kvt) {
            return hasPrefix(prefix, kvt.key) ? ADD : STOP;
        }

        public void eod() {
            this.eod = true;
        }
    }
    
    /**
     * As Prefix, and at most maxCount KVs, none for 0: stops after maxCount KVs or at the
     * first key that does not start with the prefix (the prefix's own key does; bergdb
     * 021-18).
     */
    public static class PrefixN implements StopCondition {
        private long[] prefix;
        private int maxCount;
        private int count;
        private boolean eod;
        
        public PrefixN(long[] prefix, int maxCount) {
            this.prefix = prefix.clone();     // The parameter's clone until bergdb 020-27.
            this.maxCount = maxCount;
            count = 0;
            eod = false;
        }
        
        public int handleKvt(Kvt kvt) {
            if (count >= maxCount) {
                return STOP;        // At most maxCount, none for 0, as GetN (bergdb 020-27).
            }
            count++;
            return hasPrefix(prefix, kvt.key) ? (count == maxCount ? ADD_AND_STOP : ADD) : STOP;
        }

        public void eod() {
            this.eod = true;
        }
    }
}
