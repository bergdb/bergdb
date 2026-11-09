package bergdb.pub;

/**
 * A listing of a directory's keys and values at a lookup time: the builder that
 * Connection.usePrimary(type) returns. dir() is the first call, and required; then, in any
 * order, startAt(), inclusive() and backward(), each at most once; then objects() or kvs(),
 * which may be called again. Each call is checked at once.
 *
 * <p><b>What it lists.</b> At the lookup time t, the keys of the directory's own values (not
 * its subdirectories', and never one of the database's internal keys), in key order: by
 * the names' code points (their UTF-8 bytes), ascending, or descending after backward();
 * from startAt()'s name if it was called. A key that no String key names is not listed: one
 * written through the Core API, or by another writer, whose bytes are not the bkey of
 * well-formed UTF-8 (the Core's key-encoding.md; bergdb 021-06). For each key, its value at
 * t as get(key, type) at t gives it; the keys whose value is not of the type's kind are left
 * out:</p>
 *
 * <ul>
 * <li>byte[].class: every value, its stored bytes. The array is the database's own, as
 *     get() gives it: do not change it.</li>
 * <li>Object.class: every value, as get(key, Object.class) gives it.</li>
 * <li>String.class: every value that is not an object, decoded from UTF-8 as get()
 *     decodes it.</li>
 * <li>DbObject.class, or another class: the objects, as get(key, type) gives them.</li>
 * </ul>
 *
 * <p>An object is a value at an object key (a key without a suffix, or with ".obj") that
 * is a stored object: it starts with the object format's header and passes the format's
 * full check. A byte[] put at an object key that passes that check is taken as an
 * object. So is an object of BergDB 2026.3 and before (format 1), told by its structure,
 * "bergo", the version 1, a field count and a field table that fits the value: next()
 * refuses it as get() does, and String.class leaves it out. A value that only starts with
 * "bergo" and the version 1, as a String may, is not one; a String or a byte[] whose bytes
 * happen to be a whole object of format 1, such as "bergo" and the chars U+0001, U+0000
 * and U+0000, is (bergdb 020-08, section 3).</p>
 *
 * <p><b>The lookup time.</b> t is the connection's lookup time, resolved to an actual time
 * at the call of Connection.usePrimary(), as a get() resolves it; every iterator of the
 * builder reads at t, also one made after later writes. usePrimary() is a read for
 * Connection.freezeLookupTime(): the first read after it fixes the frozen time, whether a
 * get(), an exists() or a usePrimary(). A listing does not change
 * Connection.transactionInfo().</p>
 *
 * <p>A listing whose t falls behind the first available lookup time while it runs (reclaim,
 * Database.setRetainDuration()) throws LookupTimeNotAvailableException from its iterator's
 * hasNext() or next(). After Database.stop(), an iterator throws IllegalDbStateException
 * from hasNext() or next() at its next read from the database, after the values that it
 * read before (bergdb 020-24-03, U3-5). A value that the type cannot be made from throws
 * from next() what get() throws: ObjectCreationException, or DataFormatException for a
 * value read as a String that is not well-formed UTF-8 (bergdb 021-06); the iterator can
 * go on after it.</p>
 *
 * @param <TYPE> The type of the values listed.
 * @author Frans Lundberg
 */
public interface UsePrimaryBuilder<TYPE> {
    /**
     * The directory to list, such as "/persons/", or "/" for the root: its own keys, not
     * its subdirectories'. The first call, and required.
     * 
     * @param dir  The directory; it starts and ends with '/', and has no "//" and no lone
     *     surrogate.
     * @throws IllegalArgumentException  If dir is null or not a directory.
     * @throws IllegalStateException  If dir() was called before, or objects() or kvs().
     */
    public UsePrimaryBuilder<TYPE> dir(String dir);
    
    /**
     * Whether a key whose name is startAt()'s is listed; true by default. Without
     * startAt(), it changes nothing.
     * 
     * @throws IllegalStateException  If dir() has not been called, or inclusive() was
     *     called before, or objects() or kvs().
     */
    public UsePrimaryBuilder<TYPE> inclusive(boolean inclusive);
    
    /**
     * Lists in descending key order; ascending by default.
     * 
     * @throws IllegalStateException  If dir() has not been called, or backward() was called
     *     before, or objects() or kvs().
     */
    public UsePrimaryBuilder<TYPE> backward();
    
    /**
     * The first key to list, by its name in the directory: "anna" for "/persons/anna".
     * Forward, the keys from it on are listed; backward, the keys up to it; a key of this
     * name is listed unless inclusive(false). No key needs to have the name.
     * 
     * @param name  The name: not empty, without '/' and without a lone surrogate.
     * @throws IllegalArgumentException  If name is null, empty, or has a '/' or a lone
     *     surrogate.
     * @throws IllegalStateException  If dir() has not been called, or startAt() was called
     *     before, or objects() or kvs().
     */
    public UsePrimaryBuilder<TYPE> startAt(String name);
    
    /**
     * Returns the values listed. The Iterable may be iterated several times, and objects()
     * and kvs() may be called again: each iterator lists from the beginning, at the same
     * lookup time. After the first objects() or kvs(), the builder's other calls throw
     * IllegalStateException.
     * 
     * @throws IllegalStateException  If dir() has not been called.
     */
    public Iterable<TYPE> objects();

    /**
     * Returns the values listed with their keys: Kv.key() is the key, Kv.value() the value,
     * as objects() gives it.
     * 
     * @throws IllegalStateException  If dir() has not been called.
     */
    public Iterable<Kv<TYPE>> kvs();
}

/*

Log
===


130416 Frans: Replaced exclude() method with inclusive(boolean). 


Other stuff
===========


The interface could use eq, lt, gt, lte, gte. And three value types. --> 15 different methods,
instead of eq() (3), startValue (3), backward (1), include (1) (8 methods).
Or, why not an enum for operation: 3 methods, stringCompare(Compare.GT, value)  / longCompare(...) / doubleCompare(...).
  stringValue(EQ, "first")...
  longValue(GT, 120)
  doubleValue(GTE, 1.234)
  
Would look like this:

  c.index("payments-from", Payment.class).stringValue(EQ, "1001").desc().objects();  // decreasing desc()/asc(), SQL terms
  c.index("amount", Payment.class).longValue(GTE, 1000).objects();
  
-- composite --

Is there a general way to express this also for composite indexes?

Lets focus on index usage for now. 
Note that the primary key is always part of the index. So in a way, all indexes are composite
indexes.

Limitation: for composite index a,b,c. We can search a, (a,b) or (a,b,c) specified. The restraint
for the last can be one of EQ, GT, GTE, LT, LTE, while the other ones must have EQ restraint.
The tricky thing is that we have 3 types of indexed values (string/long/double), 5 compare operations,
and 2+ parts of the composite index.

  c.index("account-from", c).select(EQ, "1001")..                    // First part by default
  
3-part composite index:

  c.index("a", c).select(0, EQ, 1001).select(1, EQ, "130101").select(2, GTE, "a")..
  c.index("a", c).select(EQ, 1001).select(EQ, "130101").select(GTE, "a")..            
      Order-dependent select calls, one per index part. Makes sense, all previous parts must
      have selector to set a new one.
      Three different selection methods for string/long/double.
       
   c.index("a", c).selectLong(EQ, 1001).selectString(EQ, "130101").selectString(GTE, "a").objects()
   
   c.index("a", c).select(1001).select("130101").select("a")..
      Same as previous, but select type inferred. Always EQ for the non-last
      For last it is one of GT/LT/GTE/LTE; default GTE.
      Changed by calling backward() and/or exclude().
      
   c.index("a", c).select(1001).select("130101").select("a").op(GT)..
      op would be one of: GT/GTE/LT/LTE/EQ_INC/EQ_DEC. Default is GTE.
      If 
   

-- Order --
When all selects are EQ, we can choose ascending/descending order. However, when last select is
not EQ (one of GT/GTE/LT/LTE), the order is given already and is not possible to change.

-- Name of GT, LT, EQ, .. --
Selector, Operator, Operation, CompareOperator, Op.GT, Select.GT, 

-- Term for forward/backward --
* forward/backward
* up/down
* ascending/descending,  asc/desc (SQL)
* increasing/decreasing, inc/dec, incr/decr


*/