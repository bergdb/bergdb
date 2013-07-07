package bergdb.core;

import java.util.ArrayList;
import java.util.List;

/**
 * Input/output to the DB.getMany() method. Also data structures and algorithms to support that
 * method. We search for KVs in interval (key1, key2].
 * If key2 == null, the interval is (key1, +inf).
 * If key1 == null, the interval is (-inf, key2].
 * 
 * @see Db#getMany(GetMany)
 * @author Frans Lundberg
 */
public class GetMany {
    
    // ---- Input ----
    
    /** 
     * Requested lookup time. 
     */
    public long lookupTime;
    
    /** 
     * First key gotten with GetMany() will be the smallest key GTE 'startKey'.
     * Use 'null' for "-inf". All keys are greater than "-inf".
     */
    public long[] startKey;
    
    /**
     * By default, GetMany returns keys greater than or equal to (GTE) 'startKey'. 
     * To use strictly greater than (GT), set this field to false.
     */
    public boolean inclusive;
    
    /**
     * By default, GetMany iterates forward (increasing keys); set this field to false
     * to iterate backwards instead.
     */
    public boolean forward;
    
    /**
     * The condition for when to stop iterating.
     */
    public StopCondition stopCondition;
    
    /**
     * Set to false to disable node caching for the GetMany operation.
     */
    public boolean cache = true;
    
    // ---- Output ----
    
    /**
     * The time used for the lookup. Possibly different from the requested lookup time.
     */
    public long actualLookupTime;
    
    /**
     * Contains a list of the resulting KVs including the time it was last written to the DB.
     */
    public final List<Kvt> result;
    
    /**
     * The GetData; used for get operations.
     */
    public final GetData gd;
    
    public GetMany() {
        result = new ArrayList<Kvt>();
        stopCondition = new DontStop();
        startKey = null;
        lookupTime = Long.MAX_VALUE;
        inclusive = true;
        forward = true;
        gd = new GetData();
    }
    
    public void setBackward() {
        forward = false;
    }
    
    // ---- Inner classes / interfaces ----
    
    /**
     * Limited access to DB.
     */
    public interface DbForMe {
        public INode followPointer(INode predecessor, int pointerIndex, 
                boolean cache, long accessData, GetData gd);

        public long getAccessData();
    }
    
    /**
     * A link in the node chain.
     */
    static class Link {
        KeyNode node;
        long compareValue;
    }
    
    /**
     * Class that implements GetMany functionality. Keeps the node chain for the iteration.
     */
    class Chain {
        // "Links" in the chain are node-compareValue pairs.
        // The links are stored in linkNodes, linkCompareValues and linkSize. More 
        // efficient then using ArrayList<Link> or something.
        
        KeyNode[] linkNodes;
        int linkSize;
        long[] linkCompareValues;
        long[] keySegments;
        int keySegmentSize;
        DbForMe db;
        KlongWithPointer kwi;
        boolean first = true;
        boolean setupEqMatch = false;
        
        private final long[] chainStartKey;
        private final boolean chainForward;
        private final boolean chainCache;
        private final boolean chainInclusive;
        
        Chain(DbForMe db) {            
            assert db != null;
            this.db = db;
            
            chainStartKey = GetMany.this.startKey;
            chainForward = GetMany.this.forward;
            chainCache = GetMany.this.cache;
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
         * 
         * @param db   Only used for testing.
         */
        void setup(KeyNode root) {
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
                    } else {
                        node.searchGte(lookupTime, startKeySegment, kwi);
                    }
                }
                
                
                if (kwi.klong == Klong.NULL) {
                    addLink(node, forward ? -1 : Long.MAX_VALUE);                    
                    break;  // Done!
                } else {
                    addLink(node, Klong.getCompareValue(kwi.klong));
                }
                
                if (node.isSegmentLeaf() && Klong.getLength(kwi.klong) < Klong.MAX_SIZE) {
                    // No need to follow, we know it is a value node pointer. Done!
                    break;
                }
                
                INode next = db.followPointer(node, kwi.pointerIndex, chainCache, 
                        db.getAccessData(), GetMany.this.gd);
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
            
            assert linkSize > 0;
            setupEqMatch = true;
            for (int i = 0; i < this.linkSize; i++) {
                if (linkCompareValues[i] != Klong.getCompareValue(start[i])) {
                    setupEqMatch = false;
                    break;
                }
            }
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
                
                INode next = db.followPointer(linkNode, kwi.pointerIndex, GetMany.this.cache, 
                        db.getAccessData(), GetMany.this.gd);
                
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
     * Implements a stop condition for DB.GetMany().
     * Can be used as a combined stop condition and filter condition.
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
         * Returns what to do with the KV. Three cases are possible.
         * 1. Add the KV to result and continue to next KV.
         * 2. Stop iterating, do not add the KV to the result.
         * 3. Continue to next KV without adding the current KV to the result.
         * 
         * @return ADD/STOP/CONTINUE/ADD_AND_STOP.
         */
        public int handleKvt(Kvt kvt);
        
        /**
         * This is called to report that the end of database was reached.
         * This method will only be called once, and handleKVT will never be called after this
         * method was called.
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
         * Non-inclusive, forward direction end point.
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
            this.key = key;
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
        
        public boolean getEod() {
            return eod;
        }
    }
    
    /**
     * Gets one KV stop condition.
     */
    public static class GetOne implements StopCondition {
        private int count;
        
        public GetOne() {
            count = 0;
        }
        
        public int handleKvt(Kvt kvt) {
            count++;
            return count > 1 ? STOP : ADD;
        }

        public void eod() {}
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
            count++;
            return count == maxCount ? ADD_AND_STOP : ADD;
        }

        public void eod() {
            this.eod = true;
        }
        
        public boolean gotEod() {
            return eod;
        }
    }
    
    /**
     * Stops when key is no longer has a given prefix.
     */
    public static class Prefix implements StopCondition {
        private long[] prefix;
        private boolean eod;
        
        public Prefix(long[] prefix) {
            this.prefix = prefix;
        }
        
        public int handleKvt(Kvt kvt) {
            return Keys.isPrefix(prefix, kvt.key) ? ADD : STOP;
        }

        public void eod() {
            this.eod = true;
        }
        
        public boolean gotEod() {
            return eod;
        }
    }
    
    /**
     * Stops at maxCount keys or when key no longer has a given prefix.
     */
    public static class PrefixN implements StopCondition {
        private long[] prefix;
        private int maxCount;
        private int count;
        private boolean eod;
        
        public PrefixN(long[] prefix, int maxCount) {
            this.prefix = prefix;
            this.maxCount = maxCount;
            count = 0;
            eod = false;
        }
        
        public int handleKvt(Kvt kvt) {
//System.out.println("GetMany.PrefixN kvt.key = " + Keys.toString(kvt.key));
            count++;
            return Keys.isPrefix(prefix, kvt.key) ? (count == maxCount ? ADD_AND_STOP : ADD) : STOP;
        }

        public void eod() {
            this.eod = true;
        }
        
        public boolean gotEod() {
            return eod;
        }
    }
}
