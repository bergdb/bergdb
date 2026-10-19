005-02. Fix M46: the top node ordinal bound
==========================================

Status: open. Kind: fix. Created 2026-10-19.


The issue
---------

Top node ordinals are bounded by `TopNode.MAX_TOP_NODE_ID_VALUE`, 2^30 − 1,
over a database's whole life. Reclaim bounds the stream but not the
ordinals. Register row M46 of
[docs/level4-alignment.md](../../docs/level4-alignment.md). The analysis,
with a patch: [item 002, 002-02](../002-top-node-ordinal-bound/02-report.md).

Why it matters now: with Level 4 the heap is a cache, so memory no longer
stops a database before the bound. A small database with a few hot keys at
1,000 transactions a second reaches it in about six months at node size 30,
five to seven weeks at node size 8; a full-speed soak on one key in 15 to 29
hours. At the bound Java fails in the worst way: in the middle of a root
split, with wrong reads, and once one more transaction commits, the database
cannot be started again (002-02, section 2).


The task
--------

Widen the ordinal as 002-02 recommends (sections 5 and 6):

1. `topNodeId` to a `long`, reading the 48 bits the stream already has
   (bytes 10 to 15 of a top node). No format change: the same bytes for
   every ordinal below 2^30.
2. A guard just below 2^48 that refuses a user transaction before it changes
   anything, so even the end is clean. (2^48 lasts centuries at the fastest
   rate measured, past the end of the database clock.)
3. Rebase 002-02's patch (7 files, 55 lines added, 32 removed, written at
   `059dbf1`) onto today's code, which item 001 changed.
4. Check the Lean model and the checker: do they bound the ordinal, or read
   it as 32 bits anywhere? The exporter and `tracecheck` must handle
   ordinals above 2^30.

Not part of this: the 2012 height decrease (002-02, section 7); it saves
bytes, does not lift the bound, and changes the format.


Done when
---------

* A database crosses 2^30, 2^31, 2^32 and close to 2^48 with restarts and
  reclaim, every historical lookup right (002-02's probes, as tests).
* The guard refuses a transaction cleanly at the end, and the database
  still restarts.
* No stream changes below 2^30: StreamDigest identical to R8's.
* The four gates print `LEVEL n OK`.
* M46 is closed in the register, item 002 is closed.


First step
----------

Apply 002-02's patch to a branch of today's code and list what no longer
fits.


Size and order
--------------

S to M. Together with 005-01 (both touch `Db.executeInner`; the bound is
one of M49's triggers).
