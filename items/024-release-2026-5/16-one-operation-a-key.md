# 024-16. One operation a key, strict

Created 2026-11-11 by Frans Lundberg. Status: open.

"One operation a key in a transaction" made strict: a transaction fails
at the commit when key transformations make two of its keys one key. In
the Core and in the Pub layer alike. This file: the rule made exact,
where it is checked and what a refusal leaves, the exception, 024-10's
table with the new results, the implementation on a branch, its tests
and gates, what BergDB's C clone must change later, and what the Lean
tree model (024-12) can assume.

Rules are S1 to S5, table rows as in 024-10, section 4 (B, T, U, P),
findings G1 to G3, questions QS1 to QS4; cite them as "024-16, S2".


## 1. In short

* **The rule.** In the builder, of the calls on one key as written, the
  last call is kept, put or delete (S1, 024-10's R1, unchanged). At the
  commit, when the key transformations make two different keys as
  written one key, the transaction is refused: nothing is written, the
  caller gets a `DbException` that names both keys as written and the key
  they became (S2). It replaces 024-10's R2 (the KV called last was kept)
  and 2026.4's rule (the last put in key order, or a delete).
* **So every transaction that reaches the index holds one operation a
  key**, with no exception and no dedup step after the sort (S3).
* **Where:** `Db.transformKeys`, new, under the write lock, after the
  transaction's time is taken and before the go point; the key
  transformations moved there from `Db.putKvs`, after the go point,
  where a refusal would have failed the database (section 4).
* **Gates** on the head `d5617d45` (on `main` at `68c3917e`):
  before-commit.sh, level1.sh and level2.sh OK; StreamDigest identical
  (section 10). **For Frans:** QS1 to QS4 (section 13), first the six
  changed expected values. State: section 15.


## 2. What is decided

Frans, 2026-11-11, 09:43: "One transaction must not set (put or delete) a
value more than once! This is a strict rule. [...] So, yes, 3, refuse it
if it happens. This is more for no-bug completeness. Won't happen in
practice, but still we want everything in the algos fixed." The
coordinator then gave three scopes and recommended B; Frans, 09:47:
"Yes!". Scope B:

* In the builder (`Trans.Builder`, and the Pub layer's calls on one key
  as written): two calls on the same key as written: the last call wins,
  put or delete, silently. This is 024-10's R1, and stays.
* At the commit: when key transformations (the Core's; key replace such
  as `${transactionTime}` in the Pub layer) make two different keys as
  written one key, the transaction fails: nothing is written, the caller
  gets an exception. In the Core and in the Pub layer alike.

It replaces 024-10's R2 (of the KVs that became one key, the one called
last is kept), which replaced 2026.4's rule (023-09, section 7.1, commit
`96a18987`: the last put in the order of the keys as written, or a
delete). It reverses Frans's choice of 2026-11-10, 17:46 ("last
operation takes precedent [...] It should be silent") for this case; he
had named the alternative himself then (17:41: "Either we should
silently use the last KV put (or delete), or we throw.").


## 3. The rule made exact

**Terms** as 024-10, section 3: a *call* is one `put` or `delete` on a
`Trans.Builder`; the *key as written* is the key the call gives; the
*final key* is the key after the KV's key transformation has run, at the
commit, when the transaction's time is known; without a transformation
it is the key as written. Only a put can have a key transformation.

* **S1. In the builder: the last call on a key as written** (024-10, R1,
  unchanged). `build()` keeps, for each key as written, the call made
  last on it, a put with its value and transformations or a delete;
  the earlier calls on that key are gone. Who: `build()`, by its
  `TreeMap`. So a `Trans` holds one KV a key as written. Checked by rows
  B1 to B7.
* **S2. At the commit: no two KVs with one final key.** Who: the writer
  thread in `Db.execute`, under the write lock, in `Db.transformKeys`.
  When: after `DbClock.transactionBegin` has given the transaction its
  time `t.tt` (the transformations need it), before the go point
  (section 4). How: each KV's key transformation runs, in the order of
  `t.kvs`; then `Db.sortByKey` sorts a copy of the KVs by final key, and
  two neighbours with equal final keys refuse the transaction: every
  transformed KV gets its key as written and its write hash back, the
  time is given back (`DbClock.transactionCancel`), and a `DbException`
  is thrown (section 5). Nothing of the transaction has been written to
  the index, the cache, the stream or the STM's key record. A
  transaction without a key transformation is not looked at: S1 makes
  its keys distinct, and `build()` sorts them. Checked by rows T1 to T10,
  U1, U2, P4 to P8.
* **S3. Every transaction that passes S2 reaches the index with one
  operation a key, in key order**, and every KV of it is put: there is no
  dedup step after the sort, and every KV's value transformation runs
  once. The record holds the KVs in that order, and the rerun applies
  them in stored order (024-02, section 8.4).
* **S4. Two calls are never one collision.** A KV is one element of
  `t.kvs`; the sort compares distinct elements only, so a KV is never
  compared with itself, whatever its transformation gives (an unchanged
  key too). Two elements have distinct keys as written (S1; unless the
  caller changed `t.kvs`, G1), so equal final keys mean two different
  keys as written, at least one of them transformed. A put at
  `/t/${transactionTime}.txt` called twice is one key as written: S1
  keeps the last call, and nothing is refused.
* **S5. A reused Trans.** A refused run leaves the `Trans` as it was
  before the call: its `kvs` (the same array, the same `Kv` objects,
  each with its key as written) and its `writeKeyHashes`. A run that
  commits leaves the transformed keys in it, as before (024-10, section
  11: "A reused `Trans` keeps its transformed keys", not changed). So a
  `Trans` refused once can be run again, and is refused again only if
  its transformations again make two keys one. Checked by U1, U2 and
  `testRefusedTransUnchanged`.

The rule in one sentence, for the Javadoc: of a transaction's operations
on one key as written the last one counts, put or delete; a transaction
whose key transformations make two of its keys one key is refused.


## 4. Where it is checked, and what a refusal leaves

(Written before the code; section 7 has the code.)

`Db.executeInner`'s order, in 024-10's code: `checkSize` and `warmup`
outside the lock; under it `assertDbStateIsActive`,
`refuseIfTopOrdinalsUsed`, `checkDirtyNodes`, `x.begin`,
`stmCheckConflicts`, `t.tt = dbClock.transactionBegin(...)`; then the go
point, and `putKvs()`, which first (for reclaim's steps) touches the
paths, then runs the key transformations, then `sortByKey`, then puts.
**After the go point every exception fails the database** (005-01): a
refusal in `sortByKey` there would fail it, not refuse the transaction.
So the key transformations and the check move before the go point:

* `transformKeys(t)` runs after `transactionBegin`, under the lock,
  before the go point, and gives `putKvs` the KVs to put. Nothing in
  between changes anything: `x.begin` sets the writer's per-transaction
  fields, which every transaction sets again (a `RerunException` from
  `stmCheckConflicts` leaves them the same way); `stmCheckConflicts`
  reads only.
* A key transformation that throws still fails the database, as its
  Javadoc says ("must not throw any exception"): `transformKeys` hands it
  to `fail()`, as the go point's catch did. `failInPut` in
  `DbTesterFailure` (a transformation that makes the next read fail)
  gives the same failure.
* The touch of a reclaim step now comes after the transformations. A
  reclaim step has no key transformation (`Reclaim`'s puts give none),
  so for it `transformKeys` returns `t.kvs` as it is, and nothing
  changes. An internal transaction is never refused by S2: none has a
  key transformation.

What a refusal leaves, each checked by `testRefusedTransUnchanged` and
the Pub test (section 8):

* **The database and the index:** nothing put, the go point not reached;
  every key's value at the latest time as before.
* **The stream:** nothing appended; its bytes as without the call.
* **The cache, handles, eviction:** no node made dirty or loaded under
  the lock (the warm-up before the lock may load nodes of the keys as
  written, as for any refused transaction: a load, not a change).
* **The transaction time:** `DbClock.transactionCancel` ends the
  transaction without making its time the last one; the next
  transaction may take the same time. A read that asked for the current
  time while the refused one ran got a time before it, and that time is
  kept as a time handed out (section 7, `DbClock`), so times handed out
  never go back. A lookup at `Long.MAX_VALUE` gives the time it gave
  before.
* **The STM:** no write hash recorded, so no other transaction is made
  to run again by a refused one.
* **A reused Trans:** S5.
* **The Pub layer:** the environment of a `w()` or an `rw()` is closed
  before the commit and is not run again; the `WBuilder` is spent, as
  after any exception of `execute()`.

Every way a commit is started reaches `Db.executeInner` through
`Db.execute(Trans)`: `Db.execute(Trans.Builder)`, a call from any
thread (the write lock serializes them), the Pub layer's `w()` (directly
or, with an object key, through `RwTransaction.executeRw`), `rw()`,
`Connection.put` and `delete`, and an index build's steps
(`IndexBuilderImp`, no key transformation). The Core has no other
runner of transactions. **The Pub layer's retry loop**
(`RwTransaction.executeRwInner`) catches only `RerunException`; a
`DbException` leaves it at once, so a refused transaction is not run
again, which is right: its keys would collide again.


## 5. The exception

`bergdb.pub.util.DbException`, thrown by `Db.execute` and by the Pub
layer's `WBuilder.execute()`, `Connection.rw()`, `put()` and `delete()`
as it is. Why this one:

* It is the class of every refusal of a transaction before its go point
  in which the database goes on: too large (005-17), dirty index nodes
  that no record takes (005-31), the clock out of range (005-18), the
  top node ordinals used (005-02). `Db.execute`'s Javadoc and the Pub
  API's (`WBuilder.execute`, `Connection.put`: "If the transaction is
  refused, nothing of it written, and the database goes on") list it
  for exactly that. "Too large" is the closest: a property of the
  transaction's content, found at the commit.
* Not `IllegalArgumentException`: the Pub layer's refusals of that
  class (020-14's X1, a bad key) are made at the call, from the call's
  own argument, before anything runs. Here no call is wrong by itself:
  the collision needs the transaction's time, known only under the
  write lock.
* Not `RerunException`: running again would collide again (for key
  replace, a transaction's time differs at each run, and a key written
  with a guessed time collides only by chance; a run again would mostly
  succeed, but it would hide the bug in the caller).
* Not a new subclass: nothing needs to tell this refusal from the other
  ones (question QS1).

**The message**, as a Pub user gets it for P4 with the suffix `.txt`
(`PubTester`'s run):

    Two keys of the transaction are one key after its key
    transformations: "/dt/-${transactionTime}.txt" and
    "/dt/-000000001000000008.txt" as written are both
    "/dt/-000000001000000008.txt". The transaction is refused; nothing
    of it is written, and the database goes on: a transaction has one
    operation a key (bergdb 024-16).

Each key is shown as text (`Keys.toDisplayString`), at most 100
characters of it, then `..." (N characters)`. These are the Core's keys:
the Pub layer's key `/t/x.txt` is `/dt/-x.txt` there, an object key
`/o/x` is `/do/-x` (020-08); question QS2. When more than two keys
become one key, the first two of them in the sorted copy are named: the
sort is stable, so in the order of `t.kvs`, the keys as written.


## 6. The table: 024-10's 34 cases, with the new results

024-10, section 4, rows and terms: `k` holds "old" before the
transaction, as does `$k` where named; `$k` and `~k` are keys as written
whose transformation gives `k`. "refused": `DbException`, nothing
written, `k` and `$k` hold "old". The 34 cases are B1 to B7, T1 to T10,
U1 and U2, P1 to P10, and P4 to P8 a second time with an object key.

| Row | Calls in order                          | 024-10   | Now            |
|---|---|---|---|
| B1  | put(k,1), put(k,2)                      | 2        | 2              |
| B2  | delete(k), put(k,1)                     | 1        | 1              |
| B3  | put(k,1), delete(k)                     | gone     | gone           |
| B4  | put(k,1), delete(k), put(k,3)           | 3        | 3              |
| B5  | delete(k), delete(k)                    | gone     | gone           |
| B6  | put(k,1), delete(k), put(k,2), delete(k) | gone    | gone           |
| B7  | delete(k), put(k,1), delete(k)          | gone     | gone           |
| T1  | put($k->k,1), put(k,2)                  | 2        | refused        |
| T2  | put(k,2), put($k->k,1)                  | 1        | refused        |
| T3  | put($k->k,1), delete(k)                 | gone     | refused        |
| T4  | delete(k), put($k->k,1)                 | 1        | refused        |
| T5  | put($k->k,1), put(~k->k,2)              | 2        | refused        |
| T6  | put(~k->k,2), put($k->k,1)              | 1        | refused        |
| T7  | put(~k->k,1), put(k,2)                  | 2        | refused        |
| T8  | put(k,2), put(~k->k,1)                  | 1        | refused        |
| T9  | put(k,2), put($k->k,1), delete($k)      | 2, $k gone | 2, $k gone   |
| T10 | put($k->k,1,vt1), put(k,2,vt2)          | vt2(2)   | refused, no vt |

* **T9** is not refused: S1 first, on the key as written `$k`, whose last
  call is the delete; the put at `$k` is gone before the commit, and the
  transaction is put(k,2), delete($k): two final keys.
* **T10**: neither value transformation runs (they run in the put loop,
  after the go point).

**A reused Trans**, one `Trans` run three times: its transformation
gives both KVs the final key `/shared` in runs 1 and 3, and `/later/a`
and `/later/b` in run 2.

| Row | Calls in order                          | 024-10            | Now                          |
|---|---|---|---|
| U1  | put(/template/a,1), put(/template/b,2)  | shared 2; 1, 2; 2 | refused; 1, 2; refused       |
| U2  | put(/template/b,2), put(/template/a,1)  | shared 1; 1, 2; 1 | refused; 1, 2; refused       |

**The Pub layer** (`Connection.w()`; `K` is `/t/${transactionTime}.txt`
with key replace on, `Kt` the same key with the time's digits, known to
the test by a `TestClock`; `Kt` holds "old" before):

| Row | Calls in order                          | 024-10      | Now            |
|---|---|---|---|
| P1  | put(/a.txt,new), delete(/a.txt)         | gone        | gone           |
| P2  | delete(/a.txt), put(/a.txt,new)         | new         | new            |
| P3  | put(/d,new), delete(/d), an object key  | gone        | gone           |
| P4  | put(K,a), put(Kt,b)                     | Kt = b      | refused        |
| P5  | put(Kt,b), put(K,a)                     | Kt = a      | refused        |
| P6  | put(K,a), delete(Kt)                    | Kt gone     | refused        |
| P7  | delete(Kt), put(K,a)                    | Kt = a      | refused        |
| P8  | put(Kt,b), put(K,a), put(Kt,c)          | Kt = c      | refused        |
| P9  | put(/o/1,obj), indexed field unchanged  | entry stays | entry stays    |
| P10 | put(/o/1,obj2), delete(/o/1), indexed   | no entry    | no entry       |

P4 to P8 with no suffix (an object key, `/t/${transactionTime}`): the
same, refused. After each refused row the next transaction may take the
refused one's time (section 4).

So the rows that change are exactly those where two keys as written
become one key: T1 to T8, T10, U1, U2 (runs 1 and 3), P4 to P8 with both
suffixes. Rows B, T9, P1 to P3, P9 and P10 keep 024-10's results.


## 7. The implementation

On the branch `024-16-one-operation-a-key`, on `main` at `68c3917e`
since 10:08 (first on the integration branch `024-13-int` at `524732d8`,
whose `java/`, `lean/` and `docs/` `main` holds exactly since
`a780b957`), commit `023bfa22` (`2229c812` before the rebase):

* **`Db.transformKeys`**, new, called by `executeInner` between
  `transactionBegin` and the go point: the key transformations (moved
  from `putKvs`), then `sortByKey`, then the check of neighbours. On a
  collision: the message, the keys as written and write hashes put back
  (kept before each transformation, in two arrays made only when the
  transaction has a key transformation), `dbClock.transactionCancel()`,
  `throw new DbException`. An `Error` there fails the database under the
  lock, as one before the go point does (019-40); a transformation that
  throws goes to `fail()`, as after the go point.
* **`Db.putKvs(kvs)`** takes the KVs to put; its transformation loop is
  gone.
* **`Db.sortByKey`** only sorts a copy: the comparison by `Kv.call` and
  the dedup loop are gone.
* **`DbClock.transactionCancel`**, new: ends a transaction without making
  its time the last one. `currentTime()` while a transaction runs now
  keeps the time it hands out (`transactionTime - 1`) in `lastReadTime`,
  so that after a cancel the next time is still later than every time
  handed out (Z1 of 020-23 holds). For a transaction that commits this
  changes nothing: its time is later than that time.
* **Removed with R2:** `Kv.call` and its numbering in `build()`;
  `RwEnvironmentImp`'s `LinkedHashMap`s (`HashMap`s again, as in 2026.4)
  and `writeObject`'s `remove`, which kept the order of the calls for R2.
  Looked for other uses: `Kv.call` had none; the maps' order is read only
  by `createTrans` (the builder sorts) and `indexEntries` (each object's
  entries, independent of the others'), so the order changes nothing
  (the stream: section 9). Kept: `setKv`'s `remove` (015-40, for the
  last call's key transformation) and `indexEntries`' `remove` before a
  put of an entry (for its key transformation).
* **Javadoc:** `Db.execute` (`@throws DbException`), `Trans.Builder` (the
  class, `put` with a key transformation, `build()`),
  `KeyTransformation.transform`, `Connection.setEnableKeyReplace` (024-10's
  sentence replaced: such a transaction is refused) and `rw()`,
  `WBuilder.execute`. Comments: `Dag.deleteUpward`'s Bug check (one
  operation a key: "Db.transformKeys refuses ..."), `UnlinkFuzz`'s `dup`
  mode (its code unchanged: it keeps one operation a key, as the Dag
  gets from Db).
* **`docs/sis-model.md`**, section 11, one clause: "since 024-16 a
  transaction whose key transformations make two of its keys one key is
  refused". `docs/levels.md` does not state the rule; not changed.

Size: the production code (comments and blank lines left out) gains
about 50 lines and loses about 25. What R2 needed and nothing else
needs is gone (about 15 lines). The rest of the growth is the move
before the go point, the restore that S5 asks for, the time given back,
and the message; a refusal after the go point would have failed the
database, so the move is needed whatever the check costs.

Two mutations, each built and run against `DbTester`, `DbTesterDelete`
and `PubTester`, then put back (10:01):

* M1, no restore of the keys and write hashes: fails
  `testRefusedTransUnchanged` and `testTransformedKeysSorted`.
* M2, `transactionEnd` in place of `transactionCancel`: fails
  `testRefusedTransUnchanged`, `testLastOperationWins` (the twin streams)
  and `testKeyReplaceCollisionRefused` (the next transaction's time).


## 8. Tests

**New**, in commit `023bfa22`:

* `DbTesterDelete.testRefusedTransUnchanged` (section 4's list): a Trans
  with a put, a transformed put whose final key another plain put has,
  and a delete, run twice and refused twice, from the test's thread and
  from a thread of its own. After each: the same `kvs` array, the same
  `Kv` objects with their keys as written, the same `writeKeyHashes`
  array and values, the value transformation not run, the lookup time
  and every value as before. Then a transaction that both twin
  databases run: it takes the refused one's time (`t2.tt` = the last
  time + 1), and the two streams are the same, byte for byte, after a
  restart too, at startup distances 10 bytes and 10 MB. A key of 300
  characters: the message shows 100 and "(304 characters)".
* `PubTester.testKeyReplaceCollisionRefused`: 024-10's F1 probe as a
  test (section 11 there). `/o/` with an index on `v`; `Kt` holds an
  object of `v` = 5; the four call sequences, put(K,7), put(Kt,8);
  put(Kt,8), put(K,7); put(K,7), delete(Kt); delete(Kt), put(K,7), each
  through `w()` and through `rw()`: each refused with the message; `Kt`
  still 5, `K` nothing, the index gives `Kt` 5 alone, and **one index
  entry is stored** (`IndexManager.scan` of the entries' prefix), so no
  stale entry; the `rw()` action ran once (not retried); the next
  transaction takes the refused one's time.
* `DbClock.testTransactionCancel`: the time given back, the next
  transaction at the same time; a time handed out meanwhile, then the
  clock back: the next transaction is later than it.

**Expected values changed on purpose**, in a commit of their own,
`d5617d45` (`33038dc7` before the rebase; QS4: Frans's approval). With
`023bfa22` alone the unit suite fails in these six tests, each with the
refusal's `DbException`, and no other (section 10):

* `DbTesterDelete.testLastOperationWins` (024-10's rows B and T): T1 to
  T8 and T10 refused, `k` and `$k` keep "old" (they gave 2, 1, nothing,
  1, 2, 1, 2, 1, "2!"); no value transformation runs in T10 (one ran);
  the twin database gets nothing for those rows. B1 to B7, T9 as before.
* `DbTesterDelete.testReusedTransLastCallWins` (U1, U2): runs 1 and 3
  refused, `/shared` has no value (it held the value of the last call);
  run 2 as before.
* `DbTesterDelete.testOneOperationAKeyAfterTransformations` (023-09's):
  refused; `/c/a` to `/c/e` keep "old" (they held "a2", nothing, "c1",
  "d2", "e2!"); neither value transformation runs.
* `DbTesterDelete.testReusedTransKeepsItsKvs` (023-11's F1): the first
  run, with `/shared`, refused, `/shared` has no value (it held "2");
  the second run as before.
* `DbTester.testTransformedKeysSorted` (023-09's): the transaction with
  the plain put at a transformed key is refused; the same transaction
  without it then runs, so `/t/k031` holds "newk031" (it held "plain").
  Its two Trans share the builder's `Kv` objects, so the second run also
  shows that the refusal gave the keys as written back.
* `PubTester.testLastOperationWinsRows` (024-10's rows P): P4 to P8, both
  suffixes, refused; `Kt` keeps "old" (it held b, a, nothing, a, c). P1
  to P3, P9, P10 as before.

Not changed, though they name the rule:
`DbTesterJavadoc.testTransBuilderOneOperationPerKey` (S1 only);
`DbTesterDelete.testTransformedPutsAndDeletesWithRestarts` (distinct
final keys); `DbTesterFailure.failInPut` (a transformation that makes
the next read fail: the same failure, from the first read of the put
loop after the go point, as before).


## 9. The stream's bytes

* **Core workloads without collisions: the same bytes.** StreamDigest
  `all` (level2.sh's and level3.sh's RestartInvariance configurations,
  four modes each), the base `524732d8` against the branch, both with
  the base's compiled StreamDigest: section 10. By the code: such a
  transaction has no key transformation (StreamDigest's workloads have
  none), so `transformKeys` returns `t.kvs` and `putKvs` does what it
  did.
* **Pub workloads with key replace, without collisions: the same
  bytes**, 10:03, by 024-10's probe (`PubDigest`, a Pub database on a
  `MemoryStream` with a `TestClock`, 3,000 transactions of 1 to 12
  operations through `w()` and `rw()` in turn: Strings at keys with a
  suffix, objects in a directory with an index, deletes, key replace at
  both kinds of key), compiled against each build: seeds 1, 2 and 3,
  19,638, 19,475 and 19,100 operations, streams of 2,707,096, 2,679,496
  and 2,644,192 bytes, as 024-10's. Base and branch differ in 224 bytes
  of each: 14 runs of 16 bytes at offset 24 of each meta block (every
  200,000 bytes), the database's id, which is random; the rest is the
  same. So moving the transformations before the go point and the
  `HashMap`s change no byte.
* **With collisions:** nothing; the transaction is not written. A
  workload that 024-10 wrote with a collision writes one transaction
  less now, and the later transactions may take times one lower
  (`testRefusedTransUnchanged`, `testLastOperationWins`'s twin streams).
* **No record format change**, no reader change.


## 10. Gates

Each step in a heavy-run slot of its own (`strict/gates.sh`), on the
branch's head `d5617d45` (on `main`), the first commit's step on
`2229c812` (the same files as `023bfa22`), StreamDigest against the base
`524732d8`:

| Gate                            | When           | Result                                  |
|---|---|---|
| `java/before-commit.sh`         | 11:32 to 11:33 | BEFORE COMMIT OK (91 s)                 |
| The unit suite, first commit    | 11:33 to 11:34 | the six tests of section 8 fail, only   |
| StreamDigest `all`, compare     | 11:34 to 11:35 | DIGESTS IDENTICAL (48 of 48)            |
| `java/stress/level1.sh`, full   | 11:35 to 11:37 | LEVEL 1 OK, MEM 130 (at most 131)       |
| `java/stress/level2.sh`, full   | 11:37 to 11:56 | LEVEL 2 OK, 70 traces TRACECHECK OK     |

* **before-commit.sh**: deps 9 packages; doubles 7 packages, 183 files;
  unit 1,654 tests in 47.8 s; f 89 tests in 69.8 s; demos OK (14 runs).
* **The unit suite at the first commit**: "FAILURE, total: 1654, failed:
  7": the six tests of section 8 (`testTransformedKeysSorted`,
  `testLastOperationWins`, `testOneOperationAKeyAfterTransformations`,
  `testReusedTransKeepsItsKvs`, `testReusedTransLastCallWins`,
  `testLastOperationWinsRows`), and `databasesStopped`, which names
  exactly those six as leaving a database open (each threw before its
  `close`). No other test fails.
* **StreamDigest**: "DIGESTS IDENTICAL (48 of 48; of the identical, the
  physical cut differs in 0)": section 9.
* **level1.sh**: unit 1,654; DagFuzz 300 rounds at each node size, 0
  failures; RestartStress 0 failures in each configuration;
  RestartInvariance "STREAM: identical", no checkpoint violates; MEM 130
  (at most 131): `Kv` is one int smaller, which MEM does not count.
* **level2.sh**, run because the change is in the path of every
  transaction (`executeInner`): RestartStress 0 failures; RestartInvariance
  "stream identical, all checks OK" in each configuration; CrashTest 0
  failures; BryanRepro 40 cycles, 0 failures; A2A3Check2 OK on 3,000, 500
  and 6,000 transactions, 0 adoptions below the old parent; "conformance:
  traces: 70, TRACECHECK OK: 70".
* No failure from load, so nothing was rerun.
* **Not run**: level3.sh, level4.sh, night.sh (reclaim and eviction are
  not touched; the brief asks for level1 and level2).


## 11. What C must change later

BergDB's C clone (022) follows a release, not `main`; nothing in C is
changed here. Its transformations run in `put_kvs` (`c/src/db.c`),
after its go point, in the transaction's order, with no sort yet (022-02
brings 2026.4's sort and collapse). When C is taken to release 2026.5,
with 024-10's R1 (its section 10):

* **The key transformations move before the go point**, after the
  transaction's time is taken, as `Db.transformKeys`: each pair's key
  transformation, then the sort by key (2026.4's), then a check of
  neighbours. **No collapse:** the place where 2026.4 keeps one pair of
  a run of one key refuses the transaction instead. No call number is
  needed (024-10's plan for C used the pair's index for R2; not now).
* **The refusal:** an error code of the kind C gives for a transaction
  refused before its go point (as for "too large"), with the message's
  two keys as written and the final key; each transformed pair's key
  (`tr_kv_set_key` replaced it in the transaction's memory) and write
  hash put back, so that a reused transaction runs again as Java's does;
  the time given back (C's `DbClock`, as `transactionCancel`, and its
  `currentTime` keeping the time it hands out while a transaction runs).
* **Tests:** ports of `testRefusedTransUnchanged`, of the rows B and T
  (024-16, section 6), and the changed tests of section 8 if 022-05
  ported them.
* **The cross tests** (C's and Java's streams byte for byte): a workload
  without a collision writes the same bytes as before; one with a
  collision is refused by both, so it writes nothing in both.
* **No change** of the record format, the reader or the rerun.


## 12. What the Lean tree model (024-12) can assume

024-12 models a transaction as a list of operations, `Tx.sorted` (keys
strictly increasing), with `normalize` as 2026.4's `sortByKey` rule (the
last put, or a delete) and the property 25, `NormalizeOK` (024-12,
sections 2.3 and 6). With this rule:

* **Every transaction that reaches the index has one operation a key,
  in strictly increasing key order**, with no exception: user
  transactions (S1, then S2's refusal), and reclaim's internal ones (no
  key transformation; their KVs come from a builder, S1). So `Tx.sorted`
  can be the precondition of `exec` for every transaction, and
  `normalize` is no part of the algorithm any more: no dedup step after
  the sort. If the model keeps a function from the builder's calls to a
  transaction, it is: S1 (the last call on each key), then a sort, and
  a result only when the final keys are distinct; else none.
* **A refused transaction leaves no trace**: no change of the tree, no
  record, no time (the next transaction may take its time). So the
  sequence of times of the transactions in the stream is as before:
  strictly increasing, one a transaction.
* **The delete at a node made by the transaction** (`Dag.deleteUpward`'s
  Bug check, 024-12's "one made otherwise is an error (one operation a
  key excludes it)") is unreachable by this rule, not by a dedup.
* **The rerun** applies a record's operations in stored order, which is
  the key order of distinct keys: the same precondition.


## 13. Findings and questions

* **G1. A Trans changed by its caller is not checked.** `Trans.kvs` and
  `writeKeyHashes` are public fields: a caller can set `kvs` to KVs out
  of key order, or with two at one key and no key transformation, which
  no check refuses (`transformKeys` looks only at a transaction with a
  key transformation; `Db.execute`'s Javadoc: "Assumption: t.kvs is
  sorted"). Two KVs at one key then reach the Dag (the Bug of
  `Dag.deleteUpward`, or a wrong tree). Old, not changed here; it is the
  one way left to give the index two operations a key. A check of every
  transaction would cost a compare of neighbours, n - 1 key compares a
  transaction: question QS3.
* **G2. The message shows the Core's keys** (section 5): a Pub user sees
  `/dt/-...` for `/t/...`. The Core knows nothing of the Pub layer's
  keys (010-01, P12); the Pub layer could catch the refusal and say it
  in its own keys, or the exception could carry the keys: question QS2.
* **G3. A reused Trans that commits keeps its transformed keys** (024-10,
  section 11, old): its next run's transformations see the keys the
  last run left. A refused run gives the keys as written back (S5), so
  the two cases differ. Giving them back always would cost nothing
  more, and make a reused Trans run the same each time; not done, as it
  changes a committed run's behaviour: question QS4's second part.

Questions for Frans, each with the choice made so that the work does
not wait:

* **QS1. The exception: `DbException`**, the class of every refusal
  before the go point (section 5), not `IllegalArgumentException` and
  not a new subclass. Chosen: `DbException`.
* **QS2. The message in the Pub layer's keys** (G2)? Chosen: not now; the
  Core's message names the keys as the Core has them.
* **QS3. Check every transaction for one operation a key** (G1), also
  one without a key transformation, as a guard against a `Trans` changed
  by its caller? Chosen: not now; an entry of its own if wanted.
* **QS4. The six changed expected values** (section 8, commit
  `d5617d45`): Frans's approval. And G3: give a committed Trans its keys
  as written back too? Chosen: no, not in this item.


## 14. Log

2026-11-11, 09:48. Started, by an agent of coord-1111 ("strict"). Read:
the common brief, 024-10 in full, 023-09 (section 7.1), 020-14 (X1, the
Pub layer's refusals), 024-12 (sections 2.3 and 6), and the code:
`Db.execute`, `executeInner`, `putKvs`, `sortByKey`, `fail`, `checkSize`,
`DbClock`, `Trans`, `Kv`, `KeyTransformation`, `RwEnvironmentImp`,
`RwTransaction`'s retry loop, `WTransaction`, the Pub API's Javadoc,
the C clone's `put_kvs`. Clone made, branch from `024-13-int` at
`524732d8`.

09:53 to 09:56. Sections 1 to 6 written, before any code. Found then:
the transformations ran after the go point, where a refusal fails the
database; so they move before it (section 4).

09:56 to 10:02. The change; the new tests; the six existing tests fail
as read beforehand; commit `2229c812`; the six expected values changed,
commit `33038dc7`; the mutations M1 and M2; the affected testers pass
(304 tests). 10:03: the Pub stream probe (section 9), the base worktree
built. 10:03: a background command waits for `int-gates-done` and the
lock, then runs the gates (`strict/gates.sh`).

10:08. Rebased onto `main` (`68c3917e`, which holds `524732d8`'s
`java/`, `lean/` and `docs/` since `a780b957`); the same content. Until
10:51 the lock was taken by others ("tie", "thr", the integration). 10:52:
the waiting loop replaced by `slot.sh` (two slots since 10:50), one slot
for each gate step. 11:21: `slot.sh take` waited for ever, as its grep for
"timing" matches an owner file's "not timing"; `gates.sh` got its own
take that skips such lines (told the coordinator), and before-commit.sh
first. 11:32 to 11:56: the gates, all as expected (section 10).


## 15. State

2026-11-11, 11:58, by an agent of coord-1111 ("strict"). The work of the
brief is done; the branch waits for Frans's answers and the
coordinator's landing.

* **Done.** The rule (section 3), where it is checked (section 4), the
  exception (section 5), the table (section 6); the change and the new
  tests, commit `023bfa22`; the six changed expected values, commit
  `d5617d45` (sections 7 and 8); the stream's bytes (section 9); the
  gates, all OK (section 10); C (section 11) and the Lean tree model
  (section 12); findings and questions (section 13).
* **Not done.** Nothing of the brief. Not asked for: G1 to G3's changes,
  level3.sh and level4.sh, the C clone, 024's readme (its line for this
  file is the coordinator's), release notes (`releases/next.md` does
  not name 024-10's rule either).
* **For Frans.** QS1 to QS4 (section 13); QS4 first: the six changed
  expected values of commit `d5617d45`.
* **Where.** Clone `/Users/f/fl/bench/2026-11-11/strict/clone`, branch
  `024-16-one-operation-a-key`, on `main` at `68c3917e` (rebased at
  10:08; before, on `524732d8`, the head of `024-13-int`, whose `java/`,
  `lean/` and `docs/` `main` holds exactly since `a780b957`), head
  `d5617d45`, two commits (`023bfa22`, `d5617d45`; before the rebase
  `2229c812`, `33038dc7`, the same content); the working tree clean;
  nothing pushed. Worktrees: `strict/base` (`524732d8`, built, for the
  byte comparisons) and `strict/c1` (`2229c812`, for the unit suite of
  the first commit). The gate script `strict/gates.sh`, its log
  `strict/gates.log`, the outputs `strict/unit-c1.txt`, `sd-base.txt`,
  `sd-cur.txt`, `bc.txt`, `l1.txt`, `l2.txt`; the Pub probe and its
  streams: `strict/probes/`. No slot is held by this work.
* **To continue.** To land: the two commits on `main` (the
  coordinator), after Frans's word on QS4; if `main` has moved in
  `Db.java`, `DbClock.java`, `Trans.java`, `Kv.java`,
  `RwEnvironmentImp.java`, the Pub API's `Connection.java` or
  `WBuilder.java`, or the testers, rebase and run before-commit.sh
  again. If Frans chooses otherwise on QS1 (another exception class):
  `Db.transformKeys`'s throw, the Javadoc of section 7 and the tests'
  catches.
