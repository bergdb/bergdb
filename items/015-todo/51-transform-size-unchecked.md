015-51. Fix: a value transformation's result is not size-checked: one above the value limit fails the database
==============================================================================================================

Status: done (decided 2026-11-05: the caller's fault, R7's first option).
Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review R7's finding R7-F2 (items/016-release-2026-2/06-reviews/R7.md,
section R7-F2: where, intended, actual, effect, a proposed fix), shown by a
probe in 06-reviews/R7/. No second agent has checked it yet.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. Done in the night 006-12 (W1, clone `g3a`), by R7's first option: the
contract is written down, the code is unchanged. Verified with R7's probe as a test:
`Db.checkSize` counts `kv.getValue()`, the transformation's input, before the go
point; `putKvs` runs the transformation after it, and a result whose record passes
the record limit makes `StoredTrans`'s record check throw in `store()`, which fails
the database ("The record of the transaction would take 120112 bytes, more than the
limit, 100000").

* Why not R7's second option, the transformations run before the go point so that
  their results can be refused: a transformation takes the transaction's time, known
  only at the go point (`dbClock.transactionBegin()`), and the one transformation
  BergDB itself uses, the row of a reclaim step (`Reclaim.step`), stores the bytes of
  the index nodes that the step's touch and puts made dirty (`Trans.dirtiedBytes`),
  known only after `putKvs`'s puts. A check in `putKvs` cannot refuse either: it is
  after the go point. A check there against `valueLimit()` would fail databases that
  now commit (a result above 7/8 of the limit whose record still fits).
* Javadoc: `ValueTransformation.transform` says that its result is not size-checked,
  that it must keep the transaction's value nodes within `StoredTrans.valueLimit()`
  as a value given directly must, and that a larger result is the caller's fault, as
  an exception is: one whose record does not fit fails the database when the record
  is made, and the transaction is not in the stream. `KeyTransformation.transform`
  says that its new key is not checked either. docs/levels.md, section 3 (the go
  point), says it. A line in `releases/next.md` (Documentation).
* Test: `DbTester.testTransformedValueBeyondRecordLimit` (unit), the probe's case
  with the record limit at 100 kB: the transformation returns 120,000 bytes; the call
  throws `DbFailedException` whose cause names the record limit, the next transaction
  is refused, and a restart on a copy has `/a`, not `/t`, and takes a commit. It pins
  the contract now stated; it passes before and after, as the code is unchanged.
* 010-01: no departure; P7 (a failed database stops) holds for the caller's fault.
  The Pub API uses no value transformation, so only Core API users can meet it.
* For Frans: this keeps a database failure for a Core API caller's oversized
  transformation result, as for its exception. If he wants such a result refused
  instead, it needs a design of when transformations run (and of reclaim's row);
  not tonight.

2026-11-05, 21:03. Frans, to the coordinator of the night 006-12, which asked him to
accept R7's first option ("a") or to have such a result refused instead ("b": a
redesign of when transformations run): "'a' for 015-51. And also add the possibility
of a refusal to the to-consider list of the long-term item." Option (a): a value
transformation's result above `StoredTrans.valueLimit()` is the caller's fault, as an
exception from the transformation is; one whose record does not fit fails the
database (P7), and the transaction is not in the stream. Decided; nothing in `java/`
changed after b185a73. Out of 018-01's list of the Core's faults (section 3.1);
harness 6.4 counts such a result as the caller's fault (018-01, section 6.4). A
refusal is 017-07, section 3, to consider.
