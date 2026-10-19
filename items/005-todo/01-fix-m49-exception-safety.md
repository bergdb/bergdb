005-01. Fix M49: a transaction that throws is half committed
============================================================

Status: open. Kind: fix. Created 2026-10-19.


The issue
---------

A transaction that throws inside `Db.putKvs` is half committed. Its time
becomes readable with some of its changes in memory; the nodes it made stay
in the cache and in the writer's node list, and the next transaction writes
them as its own. Register row M49 of
[docs/level4-alignment.md](../../docs/level4-alignment.md). The full
analysis, with a reproduction, the causes in the code, the fix options and a
test plan: [item 003, 003-01](../003-transaction-exception-safety/01-finding.md).

What can trigger it: a value or key transformation that throws, an `Error`
(out of memory, an assertion), the ordinal bound (M46, 005-02), and a read
error when a put loads a node. Since Level 4 (eviction on by default) the
writer loads evicted index nodes during puts, so an I/O error in the middle
of a transaction is now an ordinary failure path, not only a lazy-startup
one. Frans decided on 2026-10-17 that it blocks nothing and is fixed later;
this is the later.


Frans
-------

Note the pre-2026 work on this. This is a central design of the database.
No roll-back of in-memory state. Instead, conditions are tested first and when a transaction
get the go signal it will always run without any exceptions thrown
as long as the required environment for the data is working; that is: 
storage, JVM, memory. And if any of those fails, the database cannot function. 
It should be restarted.



The task
--------

Fix it as 003-01 recommends, unless the work shows a reason not to:

1. **Fail-stop** (003-01, 5.1): any `Throwable` from `putKvs` or from
   `store()` marks the database failed; every later transaction is refused
   with a clear exception until a restart, which rebuilds the state from the
   stream (the restart argument, T2 and T8, already proved). Decide whether
   reads are refused too (safer) or allowed with a documented caveat.
2. **Transformations first** (003-01, 5.2): compute value and key
   transformations before the first change, so bad input to a counter does
   not stop the database. Check first whether a transformation today sees the
   earlier puts of its own transaction; the semantics must not change.
3. Clear (or assert empty) `x.transNodes` at `x.begin`.

Decide in the work: does the Lean model need to say anything? The model's
runs have no failing transactions; a fail-stop leaves the stream as the
model's run without the failed transaction, so probably no model change, but
say so explicitly in `level4-alignment.md` (row M49).


Done when
---------

* 003-01's test plan passes: the reproduction as a unit test; a put that
  fails on a read error, also with an evicted node; an exception in
  `store()`; no `two canonical objects` with assertions on.
* No stream changes when nothing throws: StreamDigest identical to R8's.
* The four gates print `LEVEL n OK`.
* M49 is closed in the register, item 003 is closed, `docs/` says what a
  failed transaction does (the public API's documentation included).


First step
----------

Reread 003-01 against today's `Db.executeInner` (item 001 changed it a lot
after 003-01 was written at `059dbf1`) and update its section 3 and 5 where
the code moved.


Size and order
--------------

S to M: the fix is small; the tests with failing reads and appends are most
of it. Do it together with 005-02, which changes `Db.executeInner` too, as
one change with one run of the gates, or as two commits in a row.
