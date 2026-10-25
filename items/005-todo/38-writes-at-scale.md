005-38. Investigate writes at scale
==================================

Status: open. Kind: investigate. Created 2026-10-24.

Found in item 004's scale tests
([004-02](../004-indirect-swizzling/02-scale-tests.md), sections 10.5.4
and 10.5.5); registered at Frans's request after the summary in
[004-03](../004-indirect-swizzling/03-summary-and-direction.md): "Register
the write problem as a todo in 005 of type Investigate."


The issue
---------

Two problems with writes into a large database, loaded with random keys
(24-byte keys, 8-byte values, 1,000 puts a transaction, a startup distance
of 10 MB):

* **The stream grows faster than the keys.** Bytes on disk per key after
  a load: 71 at 0.1M keys, 282 at 1M, 754 at 10M, 1,028 at 50M, 1,142 at
  100M, also without eviction. 004-02's likely explanation: D, bounded by
  the startup distance, holds a smaller share of the leaves as the index
  grows, so nearly every put dirties a leaf that is written again before
  another put reaches it; at 50M keys and more, about one leaf written a
  put. Not checked.
* **Loads collapse when the index does not fit the budget.** On s1 (a
  virtual disk, 0.45 ms a read): 10M keys with a 600 MB budget took an
  hour (2,800 puts a second); a 30M load reached 18.46M keys in 9 hours,
  under 100 puts a second at the end. On F53 the 100M load with an 8 GB
  budget fell from 134,000 to 20,000 puts a second. One device read a put
  would allow about 2,000 puts a second on s1, so something costs about 20
  times more. Sweeps took part: the longest sweeps of all of 004-02 were
  during loads (25 s on s1 at 10M, 266 s on F53 at 100M).

So BergDB's write cost, on disk and in time, grows with the database where
it should not, and on a slow disk a large database cannot be written at
all.


Questions
---------

1. Is the stream's growth the leaves written again, as guessed? Bytes
   written a put by kind (leaves, inner nodes, top nodes, values, meta),
   at 1M, 10M and 50M keys.
2. How does it depend on the startup distance, the transaction size, the
   node size and the key order (random against sequential)?
3. Where does a put's time go when the index does not fit: loads a put,
   device reads a put, leaf writes a put, sweeps, collections, the write
   lock?
4. Which part goes away with incremental eviction (004), and which is the
   write path's own?
5. What could fix the write path's part, and what does each cost against
   bounded startup ([007-bounds](../007-bounds/readme.md)): a larger or
   smarter D, buffering of dirty leaves, something else? What do other
   stores do here (B-trees with a write buffer, LSM trees)?


Done when
---------

A report (a subitem here, or an item of its own if it grows): the
breakdown of questions 1 and 3 measured, the share that is eviction's, and
the options for the rest with a recommendation.


First step
----------

Measure the bytes written a put by kind with ScaleBench (004-02's tool) at
1M and 10M keys in memory, and split a load with a budget into sweeps,
loads and writes, on F53 at 10M keys and on s1.


Findings
--------

2026-10-26, from item 009 ([009-03](../009-handles/03-measurements.md),
section 7), question 4 for s1 at 10M keys: the same load (600 MB budget,
2.5 GB heap, G1) took 3,015 s on release 2026.1 and 767 s on 009's branch
with handles (13,045 puts a second). 2026.1's sweeps took 119 s of it;
most of the rest was reading back what they had evicted: 10.1M stream
reads and 25.9 GB from the device, against 2.0M and 4.6 GB with handles,
whose pointers keep the node's id (no header read to find it) and whose
CLOCK eviction keeps what the writer touches. So at 10M keys on s1 the
slowness was eviction's, not the write path's. The stream's growth per key
(question 1), and loads at 30M and 100M keys, are not measured again.


Size and order
--------------

M. After the decision of 004-03 to make eviction incremental first, but
before the Lean physical layer is redone for that: if the write path's fix
changes what is pinned or written, the eviction design must know.
