package bergdb.pubimp;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;

import bergdb.core.Db;
import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.pub.DataFormatException;
import bergdb.pub.Kv;
import bergdb.pub.NoSuchIndexException;
import bergdb.pub.UseIndexBuilder;

/**
 * A scan of a user index (bergdb 020-10, section 3.4): the grammar, checked at each call; the
 * range of the entries by section 4.4's formulae; the iteration in the order of the entries'
 * keys, forward or backward, reading each entry's value at the scan's lookup time and
 * skipping a stale entry before hasNext() says true (S2-F23). The definition, the entries
 * and the values are read with Db directly, not through the connection's GetData, so a scan
 * leaves the connection's transactionInfo() as it was (N3).
 *
 * @see bergdb.pub.UseIndexBuilder
 * @author Frans Lundberg
 */
class UseIndexBuilderImp<TYPE> implements UseIndexBuilder<TYPE> {

    /** The entries a page of the iteration reads at most. */
    private static final int PAGE = 100;

    private final ConnectionImp connection;
    private final Db db;
    private final Class<TYPE> type;
    private final IndexDefinition def;
    private final char[] types;
    private final long lookupTime;          // The actual lookup time t
    private final byte[] generation;        // The prefix of the generation's entries

    private byte[] base;                    // The generation's prefix and the eq() levels
    private int k;                          // The eq() levels
    private byte[] from;                    // The level of from(), or null
    private boolean fromInclusive;
    private byte[] to;                      // The level of to(), or null
    private boolean toInclusive;
    private byte[] prefix;                  // E' of prefix(), or null
    private boolean backward;
    private boolean backwardCalled;
    private boolean done;                   // objects() or kvs() was called

    /**
     * The definition is read at the lookup time, resolved at this call (bergdb 020-10,
     * section 3.6), with IndexDefinition.read.
     *
     * @throws NoSuchIndexException  If there is no index of the name at the lookup time, or it
     *      is building then.
     * @throws ObjectCreationException  If 'type' is not a class a get takes (bergdb 020-09,
     *      section 3.3), whatever the data.
     */
    public UseIndexBuilderImp(ConnectionImp connection, String indexName, Class<TYPE> type,
            long wantedLookupTime) {
        assert connection != null;

        if (indexName == null) {
            throw new IllegalArgumentException("indexName == null not allowed");
        }
        if (type == null) {
            throw new IllegalArgumentException("type == null not allowed");
        }
        if (!type.equals(String.class) && !type.equals(byte[].class)
                && !type.equals(DbObject.class) && !type.equals(Object.class)) {
            DataObjects.checkGet(type);
        }

        this.type = type;
        this.connection = connection;
        this.db = connection.getDb();
        this.lookupTime = connection.scanLookupTime(wantedLookupTime);
        this.def = IndexDefinition.read(db, indexName, lookupTime);
        if (def == null) {
            throw new NoSuchIndexException("No index named '" + indexName + "' at the lookup "
                    + "time.");
        }
        if (!def.isActive()) {
            throw new NoSuchIndexException("The index '" + indexName + "' is building at the "
                    + "lookup time.");
        }
        this.types = def.types();
        this.generation = def.generationPrefix();
        this.base = generation;
    }

    // ======== The grammar (020-10, section 3.4) ========

    private void checkNotDone(String call) {
        if (done) {
            throw new IllegalStateException(call + " after objects() or kvs().");
        }
    }

    /** The checks of eq() on the next level, of type 't'. */
    private void eqLevel(char t, String call) {
        checkNotDone(call);
        if (from != null || to != null || prefix != null) {
            throw new IllegalStateException(call + " after from(), to() or prefix(): eq() "
                    + "comes first, one level after the other.");
        }
        if (k >= types.length) {
            throw new IllegalStateException(call + " on level " + (k + 1) + ": the index has "
                    + types.length + " levels.");
        }
        checkType(t, call);
    }

    /** The checks of from(), to() or prefix() on the level after the eq() levels. */
    private void boundLevel(char t, String call, boolean again) {
        checkNotDone(call);
        if (again) {
            throw new IllegalStateException("A second " + call + ".");
        }
        if (call.startsWith("prefix") ? from != null || to != null : prefix != null) {
            throw new IllegalStateException(call + " with " + (call.startsWith("prefix")
                    ? "from() or to()" : "prefix()") + ": a scan has a bound pair or a prefix.");
        }
        if (k >= types.length) {
            throw new IllegalStateException(call + ": no level after the eq() levels; the "
                    + "index has " + types.length + ".");
        }
        checkType(t, call);
    }

    private void checkType(char t, String call) {
        if (types[k] != t) {
            throw new IllegalArgumentException(call + " on level " + (k + 1) + ", a level of "
                    + "type \"" + IndexKeys.typeName(types[k]) + "\".");
        }
    }

    private static <V> V notNull(V value) {
        if (value == null) {
            throw new IllegalArgumentException("null is not a value of an index.");
        }
        return value;
    }

    private UseIndexBuilder<TYPE> eqLevel(byte[] level) {
        base = concat(base, level);
        k++;
        return this;
    }

    public UseIndexBuilder<TYPE> eq(long value) {
        eqLevel(IndexKeys.LONG, "eq(long)");
        return eqLevel(IndexKeys.encodeLong(value));
    }

    public UseIndexBuilder<TYPE> eq(double value) {
        eqLevel(IndexKeys.DOUBLE, "eq(double)");
        return eqLevel(IndexKeys.encodeDouble(value));
    }

    public UseIndexBuilder<TYPE> eq(String value) {
        eqLevel(IndexKeys.STRING, "eq(String)");
        return eqLevel(IndexKeys.encodeString(notNull(value)));
    }

    public UseIndexBuilder<TYPE> eq(byte[] value) {
        eqLevel(IndexKeys.BYTES, "eq(byte[])");
        return eqLevel(IndexKeys.encodeBytes(notNull(value)));
    }

    private UseIndexBuilder<TYPE> setFrom(byte[] level, boolean inclusive) {
        from = level;
        fromInclusive = inclusive;
        return this;
    }

    public UseIndexBuilder<TYPE> from(long value, boolean inclusive) {
        boundLevel(IndexKeys.LONG, "from(long)", from != null);
        return setFrom(IndexKeys.encodeLong(value), inclusive);
    }

    public UseIndexBuilder<TYPE> from(double value, boolean inclusive) {
        boundLevel(IndexKeys.DOUBLE, "from(double)", from != null);
        return setFrom(IndexKeys.encodeDouble(value), inclusive);
    }

    public UseIndexBuilder<TYPE> from(String value, boolean inclusive) {
        boundLevel(IndexKeys.STRING, "from(String)", from != null);
        return setFrom(IndexKeys.encodeString(notNull(value)), inclusive);
    }

    public UseIndexBuilder<TYPE> from(byte[] value, boolean inclusive) {
        boundLevel(IndexKeys.BYTES, "from(byte[])", from != null);
        return setFrom(IndexKeys.encodeBytes(notNull(value)), inclusive);
    }

    private UseIndexBuilder<TYPE> setTo(byte[] level, boolean inclusive) {
        to = level;
        toInclusive = inclusive;
        return this;
    }

    public UseIndexBuilder<TYPE> to(long value, boolean inclusive) {
        boundLevel(IndexKeys.LONG, "to(long)", to != null);
        return setTo(IndexKeys.encodeLong(value), inclusive);
    }

    public UseIndexBuilder<TYPE> to(double value, boolean inclusive) {
        boundLevel(IndexKeys.DOUBLE, "to(double)", to != null);
        return setTo(IndexKeys.encodeDouble(value), inclusive);
    }

    public UseIndexBuilder<TYPE> to(String value, boolean inclusive) {
        boundLevel(IndexKeys.STRING, "to(String)", to != null);
        return setTo(IndexKeys.encodeString(notNull(value)), inclusive);
    }

    public UseIndexBuilder<TYPE> to(byte[] value, boolean inclusive) {
        boundLevel(IndexKeys.BYTES, "to(byte[])", to != null);
        return setTo(IndexKeys.encodeBytes(notNull(value)), inclusive);
    }

    public UseIndexBuilder<TYPE> prefix(String value) {
        boundLevel(IndexKeys.STRING, "prefix(String)", prefix != null);
        prefix = IndexKeys.encodeStringPrefix(notNull(value));
        return this;
    }

    public UseIndexBuilder<TYPE> prefix(byte[] value) {
        boundLevel(IndexKeys.BYTES, "prefix(byte[])", prefix != null);
        prefix = IndexKeys.encodeBytesPrefix(notNull(value));
        return this;
    }

    public UseIndexBuilder<TYPE> backward() {
        checkNotDone("backward()");
        if (backwardCalled) {
            throw new IllegalStateException("A second backward().");
        }
        backwardCalled = true;
        backward = true;
        return this;
    }

    // ======== The range (020-10, section 4.4) and the iteration ========

    /**
     * The range [lo, hi) of the scan's entry keys, by 020-10, section 4.4: with base the
     * generation's prefix and the eq() levels and succ(x) the least string above every string
     * that starts with x: no bound, [base, succ(base)); from(v, true) starts at base L(v),
     * from(v, false) at succ(base L(v)); to(v, true) ends before succ(base L(v)), to(v,
     * false) before base L(v); prefix(p) is [base E'(p), succ(base E'(p))).
     */
    private byte[][] range() {
        byte[] lo = base;
        byte[] hi = IndexKeys.succ(base);
        if (from != null) {
            byte[] x = concat(base, from);
            lo = fromInclusive ? x : IndexKeys.succ(x);
        }
        if (to != null) {
            byte[] x = concat(base, to);
            hi = toInclusive ? IndexKeys.succ(x) : x;
        }
        if (prefix != null) {
            lo = concat(base, prefix);
            hi = IndexKeys.succ(lo);
        }
        return new byte[][] {lo, hi};
    }

    public Iterable<TYPE> objects() {
        done = true;
        final byte[][] range = range();
        return () -> new Iterator<TYPE>() {
            private final Scan scan = new Scan(range[0], range[1]);

            public boolean hasNext() {
                return scan.hasNext();
            }

            public TYPE next() {
                return scan.next().value();
            }
        };
    }

    public Iterable<Kv<TYPE>> kvs() {
        done = true;
        final byte[][] range = range();
        return () -> new Scan(range[0], range[1]);
    }

    /** One iteration of the scan, from the beginning, at the scan's lookup time. */
    private final class Scan implements Iterator<Kv<TYPE>> {
        private final long[] lo;
        private final long[] hi;
        private final GetData gd = db.newGetData();
        private List<Kvt> page = new ArrayList<>();
        private int i = 0;
        private long[] last = null;         // The last entry key read
        private boolean ended;              // No entry left in the range
        private String nextIkey;            // The value that hasNext() found
        private byte[] nextValue;

        Scan(byte[] lo, byte[] hi) {
            this.lo = Keys.toSegments(lo);
            this.hi = hi == null ? null : Keys.toSegments(hi);
            this.ended = hi != null && Arrays.compareUnsigned(lo, hi) >= 0;
        }

        /**
         * Looks ahead past the stale entries (020-10, section 3.4): true only if an entry
         * whose value has it as its entry is next (S2-F23).
         */
        public boolean hasNext() {
            while (nextIkey == null) {
                if (i == page.size()) {
                    if (ended) {
                        return false;
                    }
                    readPage();
                    continue;
                }
                Kvt kvt = page.get(i++);
                IndexKeys.Entry entry = IndexKeys.parseEntry(Keys.toBytes(kvt.key), generation,
                        types);
                String ikey = def.idir() + entry.fileName();
                byte[] value = db.getOne(lookupTime, Keys.toSegments(ikey), gd);
                if (value == null) {
                    continue;
                }
                byte[] levels;
                try {
                    levels = def.entryLevels(ikey, value);
                } catch (DataFormatException e) {
                    // An object of format 1 at the key: its conversion refuses it, naming
                    // the format, from next() (bergdb 020-08, step 3).
                    levels = entry.levels();
                }
                if (levels != null && Arrays.equals(levels, entry.levels())) {
                    nextIkey = ikey;
                    nextValue = value;
                }
            }
            return true;
        }

        /** The next page of entry keys in the range, in the scan's direction. */
        private void readPage() {
            page = new ArrayList<>();
            i = 0;
            final boolean[] end = new boolean[1];
            GetMany g = db.newGetMany();
            g.forward = !backward;
            if (backward) {
                g.startKey = last != null ? last : hi;
                g.inclusive = false;
            } else {
                g.startKey = last != null ? last : lo;
                g.inclusive = last == null;
            }
            g.lookupTime = lookupTime;
            g.stopCondition = new GetMany.StopCondition() {
                private int n = 0;

                public int handleKvt(Kvt kvt) {
                    boolean out = backward ? Keys.compareKeys(kvt.key, lo) < 0
                            : hi != null && Keys.compareKeys(kvt.key, hi) >= 0;
                    if (out) {
                        end[0] = true;
                        return GetMany.StopCondition.STOP;
                    }
                    n++;
                    return n >= PAGE ? GetMany.StopCondition.ADD_AND_STOP
                            : GetMany.StopCondition.ADD;
                }

                public void eod() {
                    end[0] = true;
                }
            };
            db.getMany(g);
            page = new ArrayList<>(g.result);
            if (!page.isEmpty()) {
                last = page.get(page.size() - 1).key;
            }
            ended = end[0] || page.size() < PAGE;
        }

        /**
         * The next value, converted to the scan's type as a get converts it (a conversion
         * that throws, throws from here).
         *
         * @throws NoSuchElementException  If hasNext() is false.
         */
        public Kv<TYPE> next() {
            if (!hasNext()) {
                throw new NoSuchElementException();
            }
            final String ikey = nextIkey;
            final byte[] value = nextValue;
            nextIkey = null;
            nextValue = null;

            String ukey;
            try {
                ukey = PubKeys.i2u(ikey);
            } catch (IllegalArgumentException e) {
                ukey = null;
            }
            final String finalUkey = ukey;

            // Null for a type whose get gives null for this value, as a get of a primitive's
            // wrapper over an object without the field p (bergdb 020-09, section 5.9).
            final TYPE object = connection.getDatabaseImp().getKvToObjectConverter()
                    .createObject(type, ikey, value);

            return new Kv<TYPE>() {
                public String key() {
                    return finalUkey;
                }

                public TYPE value() {
                    return object;
                }
            };
        }
    }
    
    private static byte[] concat(byte[] a, byte[] b) {
        byte[] c = Arrays.copyOf(a, a.length + b.length);
        System.arraycopy(b, 0, c, a.length, b.length);
        return c;
    }
}
