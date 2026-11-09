package bergdb.pub;

/**
 * A scan of a user index (bergdb 020-10, section 3.4): its values in the order of the index's
 * levels, then their keys, ascending or descending; the keys of equal levels by their names'
 * UTF-8 bytes, as Connection.usePrimary() lists a directory (bergdb 020-24-02, I-8). Get one
 * with Connection.useIndex(name, type), at the connection's lookup time.
 *
 * <p><b>The grammar.</b> eq() on levels 1 to k, in order (k below the index's levels for a
 * bound or a prefix; at most all levels for eq() alone); then, on level k + 1, at most one
 * from() and one to(), or one prefix(); backward() anywhere before objects() or kvs():</p>
 *
 * <pre>
 *     c.useIndex("by-from-amount", Payment.class).eq("1001").from(100, true).to(500, false)
 *             .objects();
 *     c.useIndex("by-name", Person.class).prefix("Ann").backward().kvs();
 * </pre>
 *
 * <p>Each call is checked at once. A call out of the grammar (an eq() after a bound, a second
 * from(), to(), prefix() or backward(), a level past the index's) throws
 * IllegalStateException; an argument whose Java type does not match the level's type
 * (eq(long) for a "long" level, eq(double) for "double", eq(String) for "string", eq(byte[])
 * for "bytes"), a null, a NaN, or a String with a lone surrogate throws
 * IllegalArgumentException. After objects() or kvs() every other call throws
 * IllegalStateException; objects() and kvs() may be called again, and each iterator starts
 * from the beginning, at the same lookup time. A from() above the to() in the index's order
 * gives an empty scan. -0.0 as an argument is 0.0, as the index holds it.</p>
 *
 * <p><b>The result.</b> At the scan's lookup time, the entries of the index whose levels 1 to
 * k equal the eq() values and whose level k + 1 meets the bounds or the prefix, in the order
 * of the levels and then the keys. For each, the value at its key is read at the lookup time;
 * a value whose entry is not the index's (a stale entry) is skipped, so that hasNext() never
 * says true before a next() that throws NoSuchElementException; else the value is returned,
 * converted to the scan's type as a get converts it (a conversion that throws, throws from
 * next()). A scan whose lookup time falls behind the first available lookup time while it
 * runs throws LookupTimeNotAvailableException from hasNext() or next(). After
 * Database.stop(), an iterator throws IllegalDbStateException from hasNext() or next() at
 * its next read from the database (bergdb 020-24-03, U3-5).</p>
 *
 * <p>An iterator holds nothing to release, and has no close(): no lock, no file, and no
 * hold on reclaim, whose cuts may pass its lookup time as said above; in memory, only its
 * current page, at most 100 entries, and the value it read last. So an iterator that is
 * not read to its end may be dropped (bergdb 020-24-04, U4-5).</p>
 *
 * @param <TYPE>  The type of the values returned, as for Connection.get(key, type).
 * @author Frans Lundberg
 */
public interface UseIndexBuilder<TYPE> {
    
    /** Equality on the next level, a "long" level: level 1 first, then 2, and so on. */
    public UseIndexBuilder<TYPE> eq(long value);
    
    /** Equality on the next level, a "double" level; NaN is refused. */
    public UseIndexBuilder<TYPE> eq(double value);
    
    /** Equality on the next level, a "string" level. */
    public UseIndexBuilder<TYPE> eq(String value);
    
    /** Equality on the next level, a "bytes" level. */
    public UseIndexBuilder<TYPE> eq(byte[] value);
    
    /** The lower bound on the level after the eq() levels, a "long" level. */
    public UseIndexBuilder<TYPE> from(long value, boolean inclusive);
    
    /** The lower bound on the level after the eq() levels, a "double" level. */
    public UseIndexBuilder<TYPE> from(double value, boolean inclusive);
    
    /** The lower bound on the level after the eq() levels, a "string" level. */
    public UseIndexBuilder<TYPE> from(String value, boolean inclusive);
    
    /** The lower bound on the level after the eq() levels, a "bytes" level. */
    public UseIndexBuilder<TYPE> from(byte[] value, boolean inclusive);
    
    /** The upper bound on the same level as from(), a "long" level. */
    public UseIndexBuilder<TYPE> to(long value, boolean inclusive);
    
    /** The upper bound on the same level as from(), a "double" level. */
    public UseIndexBuilder<TYPE> to(double value, boolean inclusive);
    
    /** The upper bound on the same level as from(), a "string" level. */
    public UseIndexBuilder<TYPE> to(String value, boolean inclusive);
    
    /** The upper bound on the same level as from(), a "bytes" level. */
    public UseIndexBuilder<TYPE> to(byte[] value, boolean inclusive);
    
    /**
     * The values of the level after the eq() levels, a "string" level, that start with
     * 'prefix', by code points. prefix("") takes every value of the level (bergdb 020-24-02,
     * I-8).
     */
    public UseIndexBuilder<TYPE> prefix(String prefix);
    
    /**
     * The values of the level after the eq() levels, a "bytes" level, that start with
     * 'prefix'. An empty prefix takes every value of the level.
     */
    public UseIndexBuilder<TYPE> prefix(byte[] prefix);
    
    /** Descending order; ascending by default. */
    public UseIndexBuilder<TYPE> backward();
    
    /** The values of the scan, as described in the class's Javadoc. */
    public Iterable<TYPE> objects();
    
    /** The keys and values of the scan; key() is the user's key. */
    public Iterable<Kv<TYPE>> kvs();
}
