005-68. Fix: `TransSeq.take` gets the stream's length, not where the record begins
==================================================================================

Status: dropped (2026-10-28; see Outcome: the finding does not hold, no
change). Kind: fix. Created 2026-10-28.

Registered at Frans's decision (2026-10-28, 13:09, through 006-10's
session: "as recommended", for 007-08's review), by Claude (Opus 5.5,
Claude Code).


The issue
---------

007-08's review (007-08, section "Review, 2026-10-28", point 1, and "For
Frans", 4) found that Java can leave the Lean model's bound for BergDB's
take by a meta block's 128 bytes: after a record that ends exactly on a
200,000-byte boundary, `Db.store` passes `nodeStream.getLength()` to
`TransSeq.take` as the stream's length, which would be 128 bytes before
where the next record R(i) begins (`NodeStream.getNextPos()`,
`RecoverableStream.getNextSpos()`), while the model's argument is the
latter (the meta block counted in the record before it). Java's deadline
would then be 128 bytes stricter than the model's, also its share and its
dither would differ, and since the theorems are inductions over records,
with records that each end on a boundary the difference could recur:
"for every pace" would not carry over to Java there. Proposed: pass
`getNextPos()` instead, which makes the model exact and changes a stream
only after a record that ends on a block boundary.


Done when
---------

The finding is confirmed or refuted by reading `Db.store`,
`NodeStream.getLength` and `getNextPos`, and `RecoverableStream`'s meta
blocks, and by running; if it holds: `Db.store` passes the position where
the record begins, a unit test with a record that ends on a meta-block
boundary shows the take's deadline as the model says (fails before, passes
after, if a test can show it), StreamDigest against `main` and two runs of
the new build, old databases open, 007-08's `TakeCheck.java` checked,
`java/before-commit.sh`, `java/stress/level2.sh quick` and
`java/stress/level3.sh` pass; committed. If it does not hold: why, here,
and no change.


First step
----------

Read the call site and the stream classes; check whether
`getLength()` and `getNextPos()` can differ when `take` is called.


Findings
--------

2026-10-28, by Claude (Opus 5.5, Claude Code), in a clone of `main`
(`24cc15d`, with 005-53's changes to `Db.java`).

**The finding does not hold: when `take` is called, `getLength()` equals
`getNextPos()`.** `NodeStream.getNextPos()` is
`RecoverableStream.getNextSpos()`: the underlying stream's length, or, if
that length is inside a meta block (`length % 200,000 < 128`), the end of
that block. They differ only while the stream ends at a block's start or
inside its meta block. That never happens when `Db.store` calls `take`:

* `RecoverableStream.append` writes the meta blocks eagerly. Its loop
  `while (size >= distanceToMeta)` appends the bytes up to the boundary
  and then the meta block, also when the record ends exactly there
  (`size == distanceToMeta`; its comment: "If 'size' == distanceToMeta,
  the transaction data *and* the meta block will be written together").
  After the append of a record that ends on a boundary the stream's length
  is the boundary plus 128, the position where the next record begins.
  `RecoverableStream`'s test `crashAtMetaBlockPosition` (005-27) asserts
  it: after a transaction of 199,872 bytes, `META_BLOCK_DISTANCE +
  META_BLOCK_SIZE == mstream.getLength()`, "The meta block is written with
  the transaction."
* Every append to the node stream goes through `RecoverableStream.append`
  (`NodeStream.appendNodes`; recovery's own fills, `appendZeros` and the
  header fix, use it too); `append` refuses to start inside a meta block.
* A crash can end the stream at a boundary or inside its meta block (the
  two appends can be flushed apart, 005-27), but every start runs
  `nodeStream.recover()` (`Db.startInner`) before any transaction, and
  `fixMetaBlockIfNeeded` fills that block out (005-27), so the length is
  again where the next record begins.
* The one other state is the empty stream (length 0, `getNextPos()` 128),
  where the first record is the creation's and `take` returns at once on
  an empty `TransSeq`.

So the review's case, R(i) beginning 128 bytes after the length that
`take` gets, does not arise: after a record that ends on a boundary, both
are the boundary plus 128, and the meta block is counted in that record,
as the model's cost does. The review read `getNextSpos()`'s branch for a
length inside a meta block (as 007-08's section 1 did) without the eager
write in `append` that keeps the length out of it. The deadline, the
share and the dither all get R(i)'s tpos, the model's argument.

**By running**, an instrumented copy of the clone (a check before the
call in `Db.store`, not committed: [probe.diff](68-fix-take-stream-length/probe.diff),
the lines it printed in
[probe-output.txt](68-fix-take-stream-length/probe-output.txt)):
before each `take`, count the calls, the calls where `getLength() !=
getNextPos()`, and those where the length is a boundary plus 128 (the
record before ended exactly on a boundary) with a non-empty `TransSeq`.
`StreamDigest all` (its 12 configurations in 3 modes): 88,071 calls, 0
differ, 3 after a record that ended exactly on a boundary. The unit tests
(`-ea`, "SUCCESS, 1069 successful tests"): 55,717 calls, 0 differ, 4 after
such a record. The f-tests (`-ea`, "SUCCESS, 77 successful tests"):
5,381,113 calls, 0 differ, 222 after such a record. In all, 0 of 5,524,901
calls differ, 229 of them after a record that ended exactly on a
boundary.

**Why no change, and no test.** Passing `getNextPos()` would pass the same
value in every call, so no stream would change and no test can fail
before and pass after; 007-08's `TakeCheck.java` calls `take` with a
length of its own and is not affected. The change would only make the
call site say literally what the model says, and keep it right if the
meta blocks were ever written lazily. As Frans's decision rested on the
finding, it is not made; it is a one-line change if wanted.


Outcome
-------

Dropped 2026-10-28: the review's finding does not hold, so nothing to
fix. `Db.store` passes `nodeStream.getLength()`, which at every call of
`take` equals `getNextPos()`, where the record begins, since
`RecoverableStream.append` writes a meta block together with the record
that ends at its position, and recovery fills out one that a crash cut.
The model's argument is Java's. No code, test or stream changed; no gates
needed. 007-08 notes that the meta-block gap of its section 1 and of the
review's point 1 does not arise in Java's calls of `take`.
