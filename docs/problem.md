BergDB problem statement
========================

Draft 1, 2026-10-12. Written by Claude for Frans Lundberg,
consolidated from Frans's BergDB documents 2008 to 2017; see Sources.
Each requirement says where it was stated before and what is missing.
Gaps are listed as open questions, Q1 to Q12, at the end.

Status reviewed against `ebe5f77`, 2026-10-13 18:02 CEST. This document
states requirements, not achieved guarantees. [levels.md](levels.md) is
the authority for implementation evidence; subsequent work is outside
this snapshot, except that Q9 and the reader decision of R5 were updated on
2026-10-13 after the Level 3 work (recorded in [levels.md](levels.md)). Q6,
Q7 and Q9 below are answered, retained for traceability.


Summary
=======

BergDB stores a multiversion ordered map from (key, time) to value in one
append-only stream. Lookups at any time within a retention window must take
O(log n) node accesses. Startup must take bounded time, independent of the
database size. The stream must stay within a constant factor of the data
that has to be kept. A crash must never require repair.

The core idea, self-indexed streams (invented 2009-12, described 2012):
value nodes are written to the stream at once, but index nodes are kept
dirty in memory and written only before they would fall out of a bounded
tail of the stream, the startup section. At startup, the tail is read, the
index is rebuilt as of the start of the tail, and the user transactions in
the tail are rerun.


Setting
=======

* Keys are byte strings, ordered lexicographically with bytes as unsigned
  integers. They are stored as 7-byte segments in 64-bit words, klongs
  [2012-02-segmented-keys].
* Values are byte strings, possibly empty. A delete is stored as an entry of
  its own, a tombstone.
* Time. Each transaction has a transaction time, strictly increasing. A
  lookup has a lookup time t and sees the state after the last transaction
  with a time <= t, the actual lookup time [2015-algos, section 2].
* Transactions are atomic sets of puts and deletes. Writes are serialized;
  concurrency control is optimistic (STM) with serializable isolation, and
  resident-node traversal follows direct Java references without node
  latches. Loading and installing a stream pointer uses synchronization;
  this is not a formally lock-free guarantee for every read. A stored
  transaction must be rerunnable with the same result.
* Storage is one stream that can be read at any position, appended at the
  end, and cut at the front (pretruncate) [2012-08-layers]. Nothing is
  updated in place.
* Target: memory is much smaller than the data. Some state must be in memory
  for correctness (the dirty index nodes); the rest should be evictable
  cache. Level 4 is not implemented, so the current Java code does not yet
  meet this memory requirement.

Symbols:

    n_t   number of live keys at time t; n = n_now
    N     total number of versions stored, all (key, time) entries
    L     total size of the live data (keys and values) now
    D     startup distance: target length of the startup section in bytes
    R     retention duration: how far back in time lookups must work
    B     node capacity in klongs (maxNodeSize, default 30)
    f     reclaim value/index byte allowance / stream growth (internalFraction)


Requirements
============


R1 Lookups
----------

get(k, t) returns the value of key k at time t, or none. Also EQ, LT, LTE,
GT and GTE searches, and ordered scans in both directions from a key at a
fixed time. All for every t in the retention window [now - R, now].

Target cost: O(log_B n_t) node accesses for a get, plus O(m / B) for a scan
returning m entries, times a factor for long keys (one tree per segment).

Stated: v5 ("O(log(N)) access time to a specific item given its key");
2015-algos, section 3.2 ("O(log(N)) searches (EQ, LT, LTE, GT, GTE) for any
lookup time"); startup.md (paths of length O(log(size))).

Status: the lookup bound is claimed, not proved for BergDB. N in the older
claims is ambiguous; the symbols above distinguish keys from versions.
Latest and historical lookups pass the tests in [levels.md](levels.md).
See Q1 to Q3.


R2 Crash safety and atomicity
-----------------------------

The stream can be cut at any position, and the result is a valid database in
the state after the last complete transaction. Startup after a crash needs
no repair. A transaction is visible completely or not at all.

Stated: v5 (third requirement); bergdb.com/about.html ("Crash proof");
2014-08-startup (meta blocks every 200,000 bytes).

Status: byte-cut crash recovery passes the recorded Java model checks,
including after reclaim cuts. Lean proves recovery only for a prefix of
complete abstract records. `execute()` appends to a buffer; the application
must sync for the configured durability level. The existing buffer-delay
design is retained. Power-loss durability and the OS/device flush path
remain to be validated; see [levels.md](levels.md), "Level 2 under load".


R3 Bounded startup
------------------

Startup reads only the startup section, the last D bytes or so of the
stream, and reruns the user transactions in it. The target is recovery
bounded by D rather than the whole stream. A strict O(D) time claim also
needs bounds on replay's tree accesses, transaction work and startup lag.

Stated: v5 (startup distance, "200 MB is used a typical value"); startup.md
(requirement 4: "O(1), or at least not greater than O(log(G.size()))");
about.html (about 1.5 s for 1, 10 and 100 million entries); log 2016-04-12.

Status: algorithm and proof sketch in startup.md. Correctness of the
startup (recovery and restart invariance) is now proven in Lean for an
abstract model ([sis-model.md](sis-model.md)), with the exact still-dirty
test. Level 2 Java passes the tests run, including load and crash checks,
but refinement to that model is still open ([levels.md](levels.md)).
Measured startup was 0.62 s for a 1.6 GB stream and 0.70 s for 18.5 GB,
with a 20 MB startup distance. The bound is open: in the code, the startup
section can grow beyond D when many index nodes wait to be written: a
fairness limit in TransSeq.take() caps the nodes written per transaction,
and nothing bounds the lag. See Q4.


R4 Write overhead
-----------------

Bounded startup has a price: dirty index nodes must be written before they
leave the startup section. The bytes appended per user byte (the stream
overhead, or write amplification) must be bounded.

Stated: v5 (stream overhead below 0.7 for typical applications); log
2016-04-12 ("the append overhead will *not* be O(1), but something like
O(log(N / S)) where N is the total number of nodes and S is the number of
nodes in the startup section").

Status: measured on 13 October at 6.0 and 9.9 stream bytes per user byte
with uniform updates at 1M and 10M keys, and lower for a hot set or larger
startup distance. Reclaim has separate cost grids. A bound still needs a
model of D, n, B and the update pattern; see Q5 and [levels.md](levels.md).


R5 Space and reclaim
--------------------

The stream must not grow forever. Versions older than the retention window,
and deleted keys, must eventually be removed by cutting the front of the
stream, so that

    stream length <= c * (L + history within R)

while reclaim stays within a specified maintenance budget. The current
internalFraction f budgets estimated value-node bytes and index nodes made
dirty by a step against stream growth, which itself includes reclaim.
Table/record overhead and later still-dirty rewrites remain excluded.
The 16 KB scan target limits step size but can be exceeded by the final KV;
neither setting proves a cap on total reclaim writes or latency. A measured
attribution of the stream bytes is in [levels.md](levels.md), "Level 3 cost".

Stated: 2012-07-space-reclaim (iteration table, tRetain, write fraction,
and "Case A": stream between 2 and 4 times the live data at f = 0.5);
Reclaim.java. Excluded from every theory document: v5, 2014-08-startup,
2014-08-kv-stream, 2015-algos, startup-1604.md and startup.md.

Status: a design note and code, no proof. Off by default since 2013-07-07
(retain forever). Tested and reworked 2026-10-13: it works in all tests run,
with restarts and crashes, and Q6 and Q7 were bugs, now fixed. The initial
repair kept 8 to 12 times the live data in one load experiment. The reviewed
baseline adds retention pacing, separate current-row storage, an older
cut point, index-aware budgeting and a 16 KB scan target. Its WE/SE grids
are in [levels.md](levels.md), "Level 3 cost". Remaining efficiency tradeoffs,
total-write budgeting remain open. Readers overlapping cuts: such a read may
expire with a LookupTimeNotAvailableException (decision D1 = A, 2026-10-13);
protected reads are a later option. See [levels.md](levels.md), "Level 3 follow-up".
The new [Level 3 plan](level3-plan.md) covers power loss, the disk soak and
the performance reference before Level 4. Infinite retention remains the
default, and finite retention schedules reclaim.
The older 8–12 figure is not a final performance claim. See Q6 to Q9.


R6 Memory
---------

The in-memory state needed for correctness, the set of dirty index nodes (D,
the TransSeq), must be bounded: O(D), or the number of index nodes changed
within the startup section. Everything else is cache. A node may be evicted
from memory only if it is clean and has a retained, complete backing
version, with ownership and in-flight operation requirements satisfied.

Stated: log 2016-04-12 ("A node may be evicted iff it is clean");
2012-04-cache-eviction.

Status: Level 4 is not implemented; a refcounting cache was started in
2017-07. The 13 October load tests show heap growth with history. The
[Level 4 proposal](level4-plan.md) identifies version authority, coherent
pointer publication and bounded retirement as design gates. Cleanliness
alone is not sufficient to release an object. See Q10.


R7 Cache-awareness
------------------

Constant factors matter: nodes sized to a few cache lines (30 klongs, 240
bytes), linear search within a node, integer comparisons of key segments,
few pointer dereferences per lookup. Measured: about 1 microsecond per get
in a database of 1 million entries in memory (about.html, 2014).

Stated: 2012-01-optimal-tree-structure, 2012-01-the-separator-problem,
2012-02-segmented-keys, 2012-05-linear-search, about.html.

Status: current warm gets measured about 1 us at 1M and 10M keys, but cold
loads are slower ([levels.md](levels.md)). There is no cost model. A theory
could state the bounds in the external-memory model with block size B and
leave constants to measurement.
See Q3.


Not part of the problem
-----------------------

No query language, access control, sharding or distribution. Secondary
indexes, replication, encryption and the mapping of Java objects are built
on top of the map and are left out here.


Invariants to prove
===================

INV-LOOKUP. For every time t in the retention window and every key, a lookup
returns the value of the last put of the key with a time <= t, or none if
there is no such put or the last change is a delete.

INV-RESTART. A restart between any two transactions changes nothing: not the
lookups, not the dirty set D, not even the bytes later appended to the
stream. This is Frans's goal from 2015-12-28: "a restart can be inserted
between any two transactions without affecting the bytes in the stream".
See [sis-model.md](sis-model.md) for the abstract proof and
[levels.md](levels.md) for Java evidence and remaining obligations;
[startup-invariants.md](startup-invariants.md) is the historical analysis.

INV-CRASH. Cutting the stream at any position gives the database state after
the last complete transaction before the cut.

INV-RECLAIM. Reclaim never cuts away a stream position that a lookup with a
time in the retention window can reach.

INV-EVICT. Only eligible clean, backed nodes may be unloaded. Reloading
preserves admitted lookups, subsequent writes and restart invariance.
Ownership, pins, version authority and stream lifetime are additional
eligibility conditions; see [level4-plan.md](level4-plan.md).


Open questions
==============

Q1. What is n in O(log n)? Nodes are split (time splits and space splits)
but never merged; there is no merge code at all. After many deletes, the
tree keeps the size it once had, and nodes with no live keys stay in it.
An n_t bound cannot be inferred from this design; the historical size of
the tree also matters. No replacement bound in the largest live-key count
has been proved here. The multiversion B-tree (Becker et al. 1996) merges
underfull nodes and gets O(log_B n_t). Decide which bound BergDB should promise.

Q2. Long keys. Each 7-byte key segment has its own tree, so a key of length
l costs a number of tree searches proportional to l/7, with segment-boundary
and empty-key encoding included. State the bound with key length as a
parameter.

Q3. Cost model. Define the cost of a lookup (node accesses, cache misses,
stream reads) and the model used for "cache-aware".

Q4. Startup bound in practice. With the fairness limit in TransSeq.take(),
can the startup section grow without bound under a steady load? If so, the
O(D) bound needs a condition on the load, or the limit must adapt (Frans's
TODO in TransSeq.take: "increase nodeCountLimit ... if startup pos is
falling behind").

Q5. Write overhead. Derive the overhead as a function of D, n, B and the
update pattern; check the estimate O(log(N / S)) from 2016-04-12. Compare
with the measured "SS" property in the log (1.48 in 2015 and 2016).

Q6 (answered). First available lookup time after reclaim. The 2017
Reclaim.java set it to the start time of the last completed iteration.
The 2012 design says that only states after the iteration's end are complete
in the remaining
stream. Lookups between the start and the end could reach data that was cut.
Answered 2026-10-13: a bug, confirmed by test; now the end time.

Q7 (answered). Reclaim and deleted keys. The 2017 iteration rewrote live
keys only. Key nodes holding only deleted keys were never rewritten, but
stayed in the tree. After the cut, a lookup in their key range could follow a pointer
into the removed part of the stream. Answered 2026-10-13: a bug, confirmed
by test, also for the segment subtrees of deleted long keys; now each step
also makes every index node in its key range dirty. Deleted keys still stay
in the tree, so the stream keeps them (Q1).

Q8. Space bound. The earlier estimate L/f to 2L/f plus retained history
generalized the 2012 note's "Case A" (2 to 4 times at f = 0.5). It is not
a worst-case bound and does not account for all index/table overhead.
The reviewed algorithm also separates pCut from pStart and spaces starts
by R/4. Derive a bound for that algorithm and choose its budget using the
WE/SE tradeoff. The default f remains 0.25; the 2012 note proposed 0.4 to 0.7.

Q9 (answered). Reclaim rewrites live values with a new time. A value's "last
written time" then changes without a user transaction (noted in 2013-graph).
Independently, `Kv.time()` reported the time of a key-node entry, which after a
time split of the key node is the time of the split, not of the write, even
without reclaim. Answered 2026-10-13 (Frans): there is no exact value time in
the product. `Kv.time()` and `Connection.time()` were removed from the Pub
API; `TransactionInfo.time()` (the transaction time) stays. The internal
`GetData.kvTime` and `Kvt.time` remain and are marked inexact. An exact write
time may come later: store it in the value node (a format change, +8 bytes or a
varint per value) and let reclaim copy it; then reclaim stays invisible to
users. Not planned. See [levels.md](levels.md), "Kv.time() and Connection.time() removed".

Q10. Eviction. State and prove INV-EVICT for a Dag with several parents,
including historical parents. Resolve the version-authority, publication
and lifetime gates in [level4-plan.md](level4-plan.md) before implementation.

Q11. Dead parents. When a node changes, only its current ancestors become
dirty. Old versions of dead parents still point to old versions of shared
children, and lookups for older times use them. Which versions must stay
complete, for which lookup times? Frans's "Issue 2", 2016-04-01, settled
"intuitively" on 2016-04-12. Rule R now has an abstract Lean proof; the
Java refinement and future eviction obligations remain. See the historical
startup-invariants.md, gap G2, and sis-model.md, section 11.

Q12. Novelty. Which parts are new compared with the prior art below? This is
the question Frans put to Tore Risch in 2012; it decides whether the theory
is a paper.


Prior art to check
==================

This was the initial list from Claude's knowledge. The subsequent review,
source-reading status and provisional novelty assessment are in
[prior-art.md](prior-art.md); this list is not an independent verification.

* Driscoll, Sarnak, Sleator, Tarjan: Making Data Structures Persistent.
  STOC 1986, JCSS 1989. Cited by Frans; the basis of the persistent Dag.
* Lomet, Salzberg: Access Methods for Multiversion Data (the TSB-tree).
  SIGMOD 1989. Time splits and key splits, like BergDB's time and space
  splits. Not cited.
* Becker, Gschwind, Ohler, Seeger, Widmayer: An Asymptotically Optimal
  Multiversion B-Tree. VLDB Journal 1996. Version splits, key splits and
  merges, with proven bounds. Not cited.
* Mohan et al.: ARIES. ACM TODS 1992. Redo starts at the oldest change not
  yet on disk (the dirty page table); writing old dirty pages moves the redo
  point forward. The same mechanism as moving the startup pos by writing
  old dirty index nodes, except that BergDB appends new versions instead of
  overwriting pages.
* Rosenblum, Ousterhout: The Design and Implementation of a Log-Structured
  File System. SOSP 1991, TOCS 1992. The segment cleaner is close to
  reclaim; checkpoint plus roll-forward is close to startup.
* UBIFS (Linux flash file system, 2008): a journal plus an index tree
  written out of place at commit; mount replays the bounded journal.
* O'Neil et al.: The Log-Structured Merge-Tree. Acta Informatica 1996.
* Bernstein, Reid, Das: Hyder, a transactional record manager for shared
  flash. CIDR 2011. A log-structured multiversion tree that copies the whole
  path to the root on every update, the cost BergDB avoids.
* Levandoski, Lomet, Sengupta: The Bw-Tree. ICDE 2013; LLAMA, VLDB 2013.
  A mapping table from logical page ids to positions, another answer to the
  "path copying" problem.
* Sowell, Golab, Shah: Minuet, a scalable distributed multiversion B-tree.
  VLDB 2012. In Frans's collected papers.
* Datomic (Hickey, 2012), CouchDB's append-only B-tree, LMDB.


Sources
=======

Frans's documents. The four linked below are copied to `sources/`; the others are
in his personal archive and are not part of this repository:

* [self-indexed_streams_v5_130704.pdf](sources/self-indexed_streams_v5_130704.pdf)
  (v5). Motivation, startup distance, stream overhead, truncation; general
  linked data structures. Dated January 2012, saved 2013-07-04.
* 2014-08-startup.odt and
  2014-08-kv-stream.odt. Startup
  in five steps with pointer reconciliation; the KV-stream approach.
* [2015-algos.pdf](sources/2015-algos.pdf), dated
  2016-03-03. Data model, Dag, invariants, splits, TopDs, transactions.
* [startup-1604.md](sources/startup-1604.md), 2016-04-01,
  and [startup.md](sources/startup.md), 2016-05-05. The
  startup algorithm, the Clean Rule and the proof sketch.
* 2012-07-space-reclaim.txt.
  The reclaim design.
* one-in-skip-list.pdf
  (2012) and 2013-graph.pdf. TopDs and
  the Dag.
* 2012 design notes in doc/2012/: tree structure,
  segmented keys, linear search, cache eviction, layers.
* log.md: the development log, in particular 2015-07-19
  (theory status), 2015-11 to 2016-05 (ISSUE151111) and 2016-04-12 ("All
  theoretic issues solved!?").
* bergdb.com/about.html (Wayback Machine, 2014): the public feature list.
* Code: [Reclaim.java](../java/src/bergdb/core/Reclaim.java),
  [DbStarter.java](../java/src/bergdb/core/DbStarter.java),
  [TransSeq.java](../java/src/bergdb/core/TransSeq.java).
