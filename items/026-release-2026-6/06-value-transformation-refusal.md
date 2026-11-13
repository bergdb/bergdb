# 026-06. A value transformation that throws or passes 8 MiB refuses the transaction

Created 2026-11-13 by Frans Lundberg. Status: open (on the branch
`026-06-value-transformation`, gated, not landed; section 11).

For release 2026.6: a value transformation (Core API) that throws, or
whose result passes 8 MiB, refuses its transaction with a `DbException`
and the database goes on, as for a key transformation's refusals since
024-16 and 024-24. In 2026.5 it fails the database (024-24, QL6; 015-51;
2026.5's Known issues). Frans, 2026-11-12, 14:42: "Yes to R5 and for
2026.6. I don't see it as a bug, but something to change anyhow." (010-04,
R5; 024-35, finding 2; 026's readme.)

This file: the design, decided here by the rules R1 to R5 and 024-16's
precedent; the code, the tests and the gates; questions for Frans. Made by
the agent "vt" of coord-1113, from 08:11. Design points are D1 to D9,
questions Q1 to Q4; cite them as "026-06, D3".


## 1. In short

* **Where:** `Db.transformValues`, new, under the write lock, right after
  `Db.transformKeys` (024-16) and before the go point. A user
  transaction's value transformations run there, in the order of the
  KVs to put (key order, after the key transformations), each with the
  value as given and the key's value before the transaction, read at
  `t.tt`, as `putKvs` read it. Reclaim's own transformation (the row of a
  step) stays in `putKvs` (D2).
* **What refuses** (D4): a transformation that throws a
  `RuntimeException` (the `DbException`'s cause); a result over L4
  (8 MiB); keys and values over L5 (32 MiB), counted with the results;
  value nodes over 005-17's value limit, counted with the results. A
  `DbException`, the database goes on.
* **What a refusal leaves** (D5): nothing put, written or recorded; the
  `Trans` as before the call: each KV with a value transformation has
  its value as given again, each transformed key its key as written and
  its write hash, `t.tt` its value before; the time given back
  (`DbClock.transactionCancel`), so the next transaction may take it.
  The one `giveBack` of 024-16 does it, extended.
* **Also** (Q2, recommended and made, its own commit): a key
  transformation that throws a `RuntimeException` refuses the
  transaction in the same way; in 2026.5 it fails the database.
* **No stream change** (section 6): the same calls in the same order
  with the same inputs give the same values and the same records.
* **Gates** on `322cafed`: section 8.


## 2. What was there

`Db.executeInner` in 2026.5 (024-16, section 4): `checkSize` (L1 to L5
on the KVs as given, 005-17) and the warm-up before the lock; under it
the top node ordinals, `checkDirtyNodes` (005-31), `x.begin`, the STM's
check, `t.tt = dbClock.transactionBegin()`, then `transformKeys` (the key
transformations, the one-operation-a-key refusal, L2 and L3 and the
Core's keys on the transformed keys), then **the go point** and
`putKvs`, whose put loop ran each value transformation just before its
put: `getOne(tt, key)` for the previous value, `transform`, and for a
user transaction a result over L4 threw `IllegalStateException`. After
the go point every exception fails the database (005-01). So a
transformation that threw, a result over L4, and a result whose record
did not fit the record limit (015-51, in `store()`) failed the
database. 015-51 had decided this as the caller's fault, rule (a),
noting that a refusal needed "a design of when transformations run (and
of reclaim's row)"; 017-07, section 3 kept the refusal to consider.


## 3. The design

**D1. When: under the write lock, after the key transformations, before
the go point** (not before the lock). Who: the writer thread in
`Db.executeInner`, calling `transformValues(t, kvs, before)` right after
`transformKeys`. Why there:

* A transformation takes the transaction's time, known only from
  `dbClock.transactionBegin()`, under the lock (the reason 024-16 put
  `transformKeys` there; 015-51's first reason).
* It takes the previous value of its key, which must be the value just
  before this transaction: before the lock another writer can still
  change it, so the read must be under the lock.
* It needs the final key, after the key transformations (a KV may have
  both).
* Before the go point a refusal can still leave everything as it was;
  after it, nothing refuses (005-01).

Before the lock was the other choice: no time, no stable previous value;
refused by the transformation's own contract.

**D2. Which transactions: user transactions only.** Reclaim's internal
transactions keep their transformation in `putKvs`, after the go point,
as before: the row of a reclaim step (`Reclaim.step`) stores
`Trans.dirtiedBytes`, the bytes of the index nodes that the step's
touch and puts made dirty, known only during `putKvs` (015-51's second
reason). A step keeps its values within the limits itself (024-17,
5.5; `Trans.Builder.putLongKey`'s Javadoc), and it is BergDB's own code,
not a caller's: an exception there is a bug and fails the database
(P7), as R5 allows. How it is checked: `transformValues` is called only
`if (!t.isInternal())`, and the put loop transforms only
`if (x.trans.isInternal())`; `Reclaim`'s tests and level3's reclaim
runs (section 8) pass.

**D3. Order and inputs: those of the put loop.** The transformations run
in the order of `kvs`, the KVs to put as `transformKeys` returned them
(key order, one a key; 024-16, S3), which is the order the put loop
used. Each gets `t.tt`, the KV's value as given, and
`getOne(t.tt, key, x.getData)`, the read the put loop made. That read
gives the value before the transaction (`dbClock.lookupTime(tt)` is
below `tt`), and before the go point no put of the transaction has
happened, as in the loop no put of the same key came before (one
operation a key). So a transformation sees exactly what it saw in
2026.5, and gives the same value (section 6). The order of
transformations within a transaction changes nothing in what each
sees: a transformation sees the database before the transaction, not
the transaction's other values.

**D4. What refuses, checked by whom and when.** `transformValues`, in one
pass over `kvs` (D1's place), then two sums:

* **An exception of the transformation** (`RuntimeException`): refused at
  once, the `DbException`'s cause is the exception, message "The value
  transformation of "/k" threw (the cause). The transaction is refused;
  nothing of it is written, and the database goes on (bergdb 026-06)."
  The later transformations do not run.
* **A result over L4** (`MAX_VALUE_BYTES`, 8 MiB): refused at once, "The
  value transformation of "/k" gave a value of N bytes, more than
  8388608 (bergdb 024-17, L4). ...". A null result is a delete, as
  before (023-11, review B, B2).
* **L5 with the results** (`MAX_TRANS_BYTES`, 32 MiB): the keys (after
  the key transformations) and the values (after the transformations)
  of all the KVs, refused after the pass, "The keys and values of the
  transaction have N bytes after its value transformations, more than
  33554432 (bergdb 024-17, L5). ...". Why also L5, which the brief did
  not name: 024-17 sets L5 as the bound of a transaction's bytes, and
  024-24's review (rev24, R10) noted that results up to L4 each were not
  in L5, so L7 (the record) did not follow from L1 to L5. With L5 on the
  results, every committed user transaction is within L1 to L5 as
  stored. The precedent: `transformKeys` checks L2 and L3 again on the
  keys the key transformations give (024-24).
* **005-17's value limit with the results**: the value nodes of all the
  KVs, as `checkSize` counts them on the values as given, against
  `StoredTrans.valueLimit()`, "The transaction is too large after its
  value transformations: ... (bergdb 005-17). ...". At the release's
  record limit (2^31 - 9) L5 refuses long before it (32 MiB against about
  1.88 GB), so it binds only where a test lowers the record limit
  (`LimitsTester`, `DbTester.testTransformedValueBeyondRecordLimit`). With
  it no user transaction's value transformation can make a record that
  does not fit, which was 015-51's failure in `store()`: the record's
  value nodes are within 7/8 of the limit, and its index nodes within
  005-31's check, which counts a KV with a value transformation both as a
  put and as a delete, an over-count (unchanged).

The checks are on the values put, so a test that knows the results can
predict each refusal (`LimitsTester` does, section 5).

**D5. What a refusal gives back.** `giveBack(t, before)`, 024-16's, now
with a holder `Db.Before`, made by `executeInner` for each transaction
(one small object): `t.tt` before the call; the keys as written and the
write hashes of the KVs that a key transformation changed (filled by
`transformKeys`, null if none); the values as given of the KVs with a
value transformation (filled by `transformValues` before the first
transformation runs, null if none). `giveBack` puts back the keys, the
hashes and the values (`Kv.setValue`, new, package-private), `t.tt`,
and calls `dbClock.transactionCancel()`. So 024-16's S5 holds for value
transformations too: a refused `Trans` can be run again, and each
transformation then gets its value as given, not a result of the
refused run. A transaction that commits keeps its results in its KVs,
as before (a reused `Trans` transforms the result again, unchanged
since 2026.4). Nothing else needs undoing: before the go point nothing
has been put, made dirty, appended or recorded in the STM; the reads of
the previous values only load nodes, as the warm-up does.

**D6. Errors and failed reads still fail the database.** An `Error` from
a transformation (an `OutOfMemoryError` from a huge result, a
`StackOverflowError`) fails the database under the lock, as everywhere
(019-10, 019-40: `catch (Error e) { throw failed(e); }`); a read of a
previous value that fails on the storage fails it as any read does
(005-30, `failOnStorage`), and any other exception of that read (a bug)
through `fail(t, e)`, as in the put loop. These are a failed
environment or a bug, not a caller's mistake (R5).

**D7. Memory.** A value transformation's result was held in its KV from
the put loop until the record was made in `store()`, so all of a
transaction's results were in memory together already; now they are
from `transformValues` to `store()`, the same objects a little longer.
The reads of the previous values are the put loop's reads, made
earlier, one value at a time. New: the `Before` object (a long and three
references) a transaction, the array of values as given (one reference
a KV) only for a transaction with a value transformation. A refused
result is dropped with the exception. A transformation that returns a
huge array makes it itself (its allocation, as before); a result over L4
never reaches the Dag or the record now. No MEM change (heap per KV
kept, section 8).

**D8. The exception: `DbException`**, as L1, L3, L5, 005-17, 005-31 and
024-16's refusal: the class of a transaction refused before its go point
with the database going on (024-16, section 5), thrown by `Db.execute`
and as it is by the Pub layer (which uses no value transformation). Not
`IllegalArgumentException`: the arguments were valid at the call; the
transformation's outcome at the commit is what is refused, as for a key
transformation's key over L2 (024-24).

**D9. Key transformations that throw** (Q2): the same refusal, in
`transformKeys`: a `RuntimeException` of `KeyTransformation.transform`
gives the keys and hashes back and throws a `DbException` with the
cause, "The key transformation of "/k" threw (the cause). ..."; no
value transformation has run then. In 2026.5 it fails the database
(024-16, section 4: "A key transformation that throws still fails the
database, as its Javadoc says"). R5 covers it in the same words ("A call
of the Core API, whatever its arguments, [...] never for a caller's
misuse"), and the mechanism is the one of D5, about ten lines. The
Pub API's own key transformation (key replace) throws nothing but an
assertion's `Error`, which still fails the database. Its own commit
(`322cafed`), so that it can be left out.


## 4. The code

Branch `026-06-value-transformation` from main `ee5712c5`, in
`/Users/f/fl/bench/2026-11-13/vt/clone`, three commits on Java:

| Commit     | What                                                           |
|------------|----------------------------------------------------------------|
| `8bd6e3a7` | `transformValues`, `Before`, `giveBack`, Javadoc, new tests    |
| `f28b6832` | Tests that expected a failed database (section 5, Q1)          |
| `322cafed` | A key transformation that throws refuses too (D9, Q2)          |

* `Db.executeInner`: `Before` in place of `ttBefore`; `transformValues`
  after `transformKeys` for a user transaction.
* `Db.putKvs`: the put loop transforms only for an internal transaction;
  the after-the-go-point L4 throw (QL6) is gone.
* `Db.transformValues`, `Db.Before`, `Db.giveBack(t, before)` (section 3).
* `Kv.setValue`, package-private, for `giveBack`.
* Javadoc: `ValueTransformation.transform` (when and where it runs, in
  which order, what refuses and what fails; the rule of 015-51 replaced),
  `KeyTransformation.transform` (D9), `Db`'s "Limits" (L4's bullet and
  the paragraph on transformations), `MAX_VALUE_BYTES`, `Db.execute`'s
  `@throws DbException`, `Trans.Builder.put(key, kt, value, vt)`.
* Production code (Db, Kv; comments and blank lines left out): 121
  lines added, 23 removed, with D9; much of it the refusals' messages
  (four of them, 5 to 6 lines each), `Before` and `giveBack`.


## 5. Tests

**New** (`DbTesterLimits`; the first in `8bd6e3a7`, the last in
`322cafed`):

* `testValueTransformationThrows`: with a `TestClock`, a `Trans` of a
  plain put, a put with a key transformation (`/k` to `/kt`), a value
  transformation at `/u` that runs and one at `/v` that throws. Refused
  with `DbException`, the cause the exception, both transformations ran
  in key order; then the same `kvs` array and `Kv` objects, the keys as
  written (the transformed one given back), the write hashes, `/u`'s and
  `/v`'s values as given (the same arrays), `t.tt`; the database active,
  the lookup time, the values, the transaction count and the stream's
  length as before; the next transaction takes the refused one's time.
  Then the same `Trans` runs again and commits, each transformation given
  the value as given ("u1+u0", "v1+v0"); a restart has it.
* `testValueTransformationError`: an `Error` from a transformation is
  thrown as it is and fails the database (D6); the restart has the state
  before.
* `testTransformedValuesOverL5`: four results of 8 MiB (keys of 2 bytes)
  refused for L5 (33,554,440 bytes), the values as given back; with the
  last 8 bytes shorter, 32 MiB exactly, taken.
* `testKeyTransformationThrows` (D9): a key transformation that changes
  its key and then throws, after another one that changed its key:
  refused, both keys and hashes given back, the value transformation not
  run, nothing written, the next transaction takes the time.

**Changed expected values**, their own commit `f28b6832` (Q1, Frans's
approval). Each expected a failed database:

* `DbTesterLimits.testTransformedValueOverL4` (QL6, 024-24): the result
  over L4 now refused with the L4 message, the value as given back,
  nothing appended, the database going on; the restart has the
  transaction after it too. The result at L4 taken, as before.
* `DbTester.testTransformedValueBeyondRecordLimit` (015-51): record limit
  100 kB, a result of 120,000 bytes: refused with 005-17's message after
  the transformations (was: `DbFailedException` from `store()`, "more
  than the limit"), nothing appended, `/x` then taken; the restart has
  `/a` and `/x`.
* `LimitsTester` (harness 6.4 of 018-01): its "caller's fault" step, a
  result above the value limit, is now expected refused (`check(!callers)`
  at a commit); `refusedSize` counts the refusals "after its value
  transformations", which hold when the results' value nodes
  (`madeBytes`) pass the value limit, and a commit checks `madeBytes`
  within it. A transaction of a result near the limit and a second KV
  that together pass it is refused now (it was taken, its record still
  fitting). The run no longer ends at the fault: the code for a failed
  database after it (`callersFault`, `tainted`, the counts in the night's
  summary line) is gone, and any `DbFailedException` fails the harness,
  so the claim "the database never fails" now holds without exception.
  20 seeds of 500 steps (100 to 119): OK, 488 refused for size.
* `DbTesterFailure`: three tests used a value transformation that throws
  to fail a transaction after its go point, which it no longer does. They
  now throw from `Db.testHooks` (`TestHooks.kvApplied`, called in the
  put loop just before each put), with a helper `throwAtPut(key, thrown,
  before)`, so their claims about a failure after the go point stay:
  `testValueTransformationThrows`, renamed `testPutThrows` (003-01's
  reproduction: the second put throws after the first changed the Dag),
  `testErrorIsThrownAsItIs` (an `Error` after the go point) and
  `testWriterWaitingForTheLock`. Their asserts are unchanged.

Not changed: `DbTester.testValueTransformation1` and `2` (the time, an
atomic increment), `DbTesterDelete`'s rows with value transformations
(T10: no value transformation runs when the keys collide, still so: the
key checks come first), `DbTesterFailure.failInPut` (a key
transformation that makes the next read fail: the read fails, after the
go point, as before).

A mutation: without the values given back in `giveBack`,
`testTransformedValueOverL4` and `testTransformedValuesOverL5` fail ("the
value as given") (08:21).


## 6. The stream's bytes

No change, by the code: for a user transaction the transformations run
on the same inputs (D3) in the same order and give the same values,
which the put loop then puts in the same order, so the records are the
same; reclaim's path is unchanged. A transaction refused now (and failed
before) wrote nothing before either: a failed transaction is never in
the stream (005-01). StreamDigest's workloads and the level scripts' have
no value transformation (only `Reclaim`'s row, unchanged), so their
digests cannot change; not run (the brief's gates). No record format
change, no reader change, no Lean model change: the model has no
transformations, and a refused transaction leaves no trace (024-16,
section 12).


## 7. Documents

* Javadoc: section 4.
* `releases/next.md`: an entry under "Core API" (the change, the
  exception, what is given back, D9, the tests whose expected values
  changed).
* Not changed: 010-04's case line under R5 ("to change in 2026.6") is
  for the coordinator when this lands; 2026.5's notes (released);
  027-01 (a snapshot); 024-02 (no stream change).


## 8. Gates

On `322cafed`, the code's head, one slot at a time
(`/Users/f/fl/bench/2026-11-13/vt/gates.sh`, summary `vt/gates.out`, logs
in `vt/logs/`); the commits after it change only `items/` and
`releases/next.md`.

(Results: see State; filled in when the run ends.)


## 9. What C must change later

BergDB's C clone (012, 022) follows a release. When it is taken to
2026.6: its value transformations move out of `put_kvs` to before its go
point, after its key transformations (024-16, section 11), for user
transactions only; an error code for a transformation's failure, a
result over L4, L5 and the value limit with the results; the values as
given put back with the keys and hashes, the time given back. No stream
change.


## 10. Questions for Frans

* **Q1. The changed tests** of section 5 (`f28b6832`): approve them as a
  set. Recommended: yes. Each followed the old rule (a failed database);
  none loses a claim: `DbTesterFailure`'s failures after the go point are
  kept by a test hook.
* **Q2. A key transformation that throws refuses too** (D9, `322cafed`).
  Recommended: yes, by R5's words; made, its own commit, so the
  coordinator can leave it out if not.
* **Q3. L5 and 005-17's value limit counted with the results** (D4), not
  only L4 as the brief said. Recommended: yes; otherwise a transaction of
  500 results of 8 MiB (4 GB) still fails the database in `store()`, as
  015-51's case.
* **Q4. Reclaim's row stays after the go point** (D2). Recommended: yes;
  it is BergDB's own transformation, bounded by the step, and its value
  needs what the step's puts made dirty.


## 11. State

2026-11-13, 08:40.

* **Done:** sections 1 to 7, 9, 10; the code and tests on branch
  `026-06-value-transformation`, head `322cafed` (code), in
  `/Users/f/fl/bench/2026-11-13/vt/clone`, from main `ee5712c5`.
* **Running:** the gates (section 8).
* **To continue:** if a gate fails, read its log in
  `/Users/f/fl/bench/2026-11-13/vt/logs/`; rerun one failure alone before
  believing it (two slots). If main moves before landing: merge main,
  rerun before-commit and level1.
