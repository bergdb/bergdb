package bergdb.pub;

/**
 * A builder to create an iterator to iterate database objects in the order specified
 * by the primary index.
 *
 * <p>Experimental in 2026.3, with known faults; it may change in a later release (bergdb
 * 018-01, D6).</p>
 * 
 * @author Frans Lundberg
 */
public interface UsePrimaryBuilder<TYPE> {
    /**
     * Sets the directory to iterate.
     * 
     * @param dir  The directory; it must end with '/'.
     * @throws IllegalArgumentException  If dir is null or empty, does not end with '/', or
     *      contains "//".
     */
    public UsePrimaryBuilder<TYPE> dir(String dir);
    
    /**
     * By default, the iterator will start iterating from the start value if it exists.
     * Call this method with 'false' will exclude an exact match with start the start value
     * from the iterated entries.
     */
    public UsePrimaryBuilder<TYPE> inclusive(boolean inclusive);
    
    /**
     * By default, the iterator will iterate forward with increasing indexed value; calling this
     * method sets the iteration direction to backward (decreasing indexed value order).
     */
    public UsePrimaryBuilder<TYPE> backward();
    
    /**
     * Start value to start iterating from. By default, an exact match with 
     * 'value' will be included in the result.
     * If startAt(prefixString) has been called, 'value' is a suffix to prefixString.
     */
    public UsePrimaryBuilder<TYPE> startAt(String value);
    
    /**
     * Returns an Iterable for iterating over the objects.
     */
    public Iterable<TYPE> objects();

    /**
     * Returns an Iterable for iterating over the KVs.
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