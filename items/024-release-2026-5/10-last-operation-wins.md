# 024-10. The last operation wins

Created 2026-11-11 by Frans Lundberg. Status: done (2026-11-11): on
`main` since `36924319` (024-13); its rule R2 replaced by 024-16's
refusal (`e6e93272`); QL1 to QL5 not marked decided.

The builder's rule "the last operation wins", put or delete, in Java, for
release 2026.5 (024's readme, "Planned so far", first point; 024-01,
CA1). Frans, 2026-11-11, 07:08: "Also implement the "last operation wins"
using a separate agent." This file: the rule made exact, the cases where
release 2026.4 and the new rule differ, the implementation on a branch,
its tests and gates, and what BergDB's C clone must change later.

Rules are R1 to R6, table rows B1 to B7 (the builder), T1 to T10 (key
transformations), U1 and U2 (a reused Trans), P1 to P10 (the Pub layer),
questions QL1 to QL5; cite them as "024-10, T3".


## 1. In short

* **The rule.** In the builder, of the calls on one key as written, the
  last call is kept, a put or a delete (R1). At the commit, after the key
  transformations, of the KVs that have become one key, the one whose
  call was made last is kept (R2). Nothing else changes: one operation a
  key reaches the index, in key order.
* **Where 2026.4 differs.** Two kinds of case only (section 4): a delete
  made after a put of the same key (2026.4 keeps the put, the new rule
  deletes), and two puts that key transformations make one key, made in
  the opposite order of their keys as written (2026.4 keeps the later
  key as written, the new rule the later call).
* **The Pub API** gives the last call on a key already (015-40, 015-41);
  it differs only for keys that key replace (`${transactionTime}`) makes
  one, which needs a guess of the transaction's time.
* **Done on the branch** `024-10-last-operation-wins`: the change (about
  30 lines of production code in `Trans`, `Kv`, `Db`,
  `RwEnvironmentImp`), three new tests that hold every row of the table
  and fail on `main` at exactly the differing rows, and two existing
  tests' expected values changed in a commit of their own (section 7).
  No record format change; a transaction that names no key twice
  writes the bytes it wrote before (section 8).
* **Gates** on the branch's head `3fc470c6`: before-commit.sh, level1.sh
  and level2.sh OK (section 9). **State:** section 13.
* **For Frans:** five questions, each with the choice made (section 5);
  first the approval of the two changed expected values.


## 2. What is decided

Frans, 2026-11-10, on two KVs that key transformations make one key
(023-08, section 7; 023-09, section 7):

* 17:41: "Why keep both. [...] Either we should silently use the last KV
  put (or delete), or we throw."
* 17:46: "last operation takes precedent, put or delete. It should be
  silent"
* 17:48, on the options: "As you recommend".

The coordinator's reading of the day (023-08, section 7): in 2026.4,
silently, by the builder's rule of 015-40 (the last put, or a delete if
there is no put), so that one rule holds in the Core; "Changing the
builder's rule itself to "the last operation wins" is a later item, for
2026.5, with the C clone." 024's readme, "Planned so far": "The builder's
rule "the last operation wins", put or delete, for `Trans.Builder` as for
the KVs that key transformations make one key".

Release 2026.4's rule, for comparison:

* `Trans.Builder.build`: one KV a key as written: the last put, or a
  delete if there is no put; a delete never replaces a put, whatever
  their order (015-40; the code's comment since 2013: "Non-deletes take
  precedence over deletes").
* `Db.sortByKey` (023-09, section 7.1; commit `0b1d59f4`): after the key
  transformations and the stable sort, of the KVs with one key: the last
  put in the order of the keys as written (build's sort), or a delete if
  there is no put.


## 3. The rule made exact

**Terms.** A *call* is one `put` or `delete` on a `Trans.Builder`. The
*key as written* is the key the call gives. The *final key* is the key
after the call's key transformation has run at the commit, when the
transaction's time is known; without a transformation it is the key as
written. Only a put can have a key transformation (the builder's
`delete` takes none).

* **R1. In the builder: the last call on a key as written.**
  `Trans.Builder` numbers its calls in the order they are made, from 0.
  `build()` keeps, for each key as written, the call made last on it: a
  put with its value and its transformations, or a delete. The earlier
  calls on that key are gone, as if not made. Who: `build()`. Checked by
  rows B1 to B7.
* **R2. At the commit: the last call on a final key.** `Db.putKvs` runs
  every key transformation of the transaction first (as 2026.4), then
  `Db.sortByKey` sorts a copy of the KVs by final key and, of the KVs
  with one final key, keeps the one with the highest call number. The
  others are dropped: their value transformations do not run, they are
  not put in the index and not in the record. Checked by rows T1 to T10.
* **R3. Unchanged: one operation a key, in key order.** The index gets
  the kept KVs in the order of their final keys (023-08, Q4), and the
  record holds them in that order. A transaction where no key is named
  twice (as written or final) keeps every KV, so it runs as in 2026.4
  and writes the same bytes (section 8).
* **R4. A Trans is from one builder.** Nothing combines builders or
  `Trans` objects: `Db.execute` takes one `Trans`, and the Core has no
  call that joins two (looked for: none in `bergdb.core`, `bergdb.pub`,
  `bergdb.pubimp`). A builder built twice numbers its calls the same way
  both times, the later `Trans` with the calls made since.
* **R5. A reused Trans.** A `Trans` holds R1's result: one KV a key as
  written, each with its call number. Every run of it does R2 anew, on a
  copy (023-11, review A, F1): no KV is lost from the `Trans` by a run,
  and a KV dropped in one run is put in the next if its final key no
  longer collides. Checked by U1 and U2.
* **R6. The Pub layer.** A `WBuilder`'s and an `RwEnvironment`'s puts and
  deletes are calls in the user's order.
  * *One key as written:* the last call wins, as since 015-40 and
    015-41 (`RwEnvironmentImp`'s maps `kvOps` and `objectOps` hold one
    operation a key, the last call's, with its key transformation). A
    delete's key is taken as written (019-15).
  * *Keys that key replace makes one* (a put at
    `/t/${transactionTime}.txt` and a put or delete at the key with the
    time's digits): the last call wins, by R2. For this the maps keep
    the order of the calls (the last call on each key), and
    `createTrans` hands them to the builder in that order. In 2026.4
    they are hash maps, and the builder gets the calls in the maps'
    iteration order.
  * *Index entries* (020-10, section 5.1) are not the user's calls: at
    the commit, for the last call on each object key, the entries of
    the previous stored value are deleted and those of the new value
    put, in that order. So of a delete and a put of one entry (an
    object whose indexed fields are unchanged) the put is the last
    operation and stays, as in 2026.4 (`deleteIndexEntry`); an object
    put and then deleted leaves only the deletes of its previous
    value's entries. The entries reach the builder after the user's
    KVs, in the order of their objects' last calls. Keys with a suffix
    (`kvOps`), object keys (`objectOps`) and index entries (`indexOps`)
    are three disjoint sets of keys, also after key replace (it changes
    no `/`, no `.` and no prefix), so the order between the three maps
    decides nothing. The entries are worked out from the object keys as
    written: for object keys that key replace makes one, see section
    11, F1.

The rule in one sentence, for the Javadoc: of the operations of a
transaction on one key, the last one counts, put or delete.


## 4. The table: inputs and results

`k` is a key that holds "old" before the transaction. Calls are in the
order made. "gone" means that the key has no value after the
transaction. **Differs** marks a row where 2026.4 and the new rule give
different results.

**The builder** (`Trans.Builder`, no key transformation):

| Row | Calls in order                           | 2026.4 | New rule | Differs |
|---|---|---|---|---|
| B1 | put(k,1), put(k,2)                        | 2      | 2        |         |
| B2 | delete(k), put(k,1)                       | 1      | 1        |         |
| B3 | put(k,1), delete(k)                       | 1      | gone     | yes     |
| B4 | put(k,1), delete(k), put(k,3)             | 3      | 3        |         |
| B5 | delete(k), delete(k)                      | gone   | gone     |         |
| B6 | put(k,1), delete(k), put(k,2), delete(k)  | 2      | gone     | yes     |
| B7 | delete(k), put(k,1), delete(k)            | 1      | gone     | yes     |

**Key transformations.** `$k` and `~k` are keys as written whose
transformation gives the final key `k`; in key order `$k` < `k` < `~k`.
`$k->k` means a put at `$k` with that transformation.

| Row | Calls in order                          | 2026.4 | New rule | Differs |
|---|---|---|---|---|
| T1  | put($k->k,1), put(k,2)                  | 2      | 2        |         |
| T2  | put(k,2), put($k->k,1)                  | 2      | 1        | yes     |
| T3  | put($k->k,1), delete(k)                 | 1      | gone     | yes     |
| T4  | delete(k), put($k->k,1)                 | 1      | 1        |         |
| T5  | put($k->k,1), put(~k->k,2)              | 2      | 2        |         |
| T6  | put(~k->k,2), put($k->k,1)              | 2      | 1        | yes     |
| T7  | put(~k->k,1), put(k,2)                  | 1      | 2        | yes     |
| T8  | put(k,2), put(~k->k,1)                  | 1      | 1        |         |
| T9  | put(k,2), put($k->k,1), delete($k)      | see below | see below | yes  |
| T10 | put($k->k,1,vt1), put(k,2,vt2)          | vt2(2) | vt2(2)   |         |

* **T9**, the two steps of the rule (R1 before R2). `$k` also holds
  "old". New rule: on `$k` as written the last call is the delete, so
  the put at `$k` is gone (R1); `k` = 2, `$k` gone. 2026.4: the put at
  `$k` stays over the delete (015-40), then loses to the plain put by
  the order of the keys as written; `k` = 2, `$k` still "old": the
  delete of `$k` was lost.
* **T10**: only the kept KV's value transformation runs, once, in both.

**A reused Trans** (R5), one `Trans` run twice; its transformation gives
both KVs the final key `/shared` in the first run and `/later/a` and
`/later/b` in the second:

| Row | Calls in order, then the runs            | 2026.4          | New rule        | Differs |
|---|---|---|---|---|
| U1  | put(/template/a,1), put(/template/b,2)   | shared 2; 1, 2  | shared 2; 1, 2  |         |
| U2  | put(/template/b,2), put(/template/a,1)   | shared 2; 1, 2  | shared 1; 1, 2  | yes     |

The columns give `/shared` after the first run, then `/later/a` and
`/later/b` after the second.

**The Pub layer** (`Connection.w()`, the same for `rw()`). `K` is
`/t/${transactionTime}.txt` with key replace on, `Kt` the same key with
the digits of the transaction's time, which the test knows by a
`TestClock`.

| Row | Calls in order                          | 2026.4  | New rule | Differs |
|---|---|---|---|---|
| P1  | put(/a.txt,new), delete(/a.txt)         | gone    | gone     |         |
| P2  | delete(/a.txt), put(/a.txt,new)         | new     | new      |         |
| P3  | put(/d,new), delete(/d), an object key  | gone    | gone     |         |
| P4  | put(K,a), put(Kt,b)                     | Kt = b  | Kt = b   |         |
| P5  | put(Kt,b), put(K,a)                     | Kt = b  | Kt = a   | yes     |
| P6  | put(K,a), delete(Kt)                    | Kt = a  | Kt gone  | yes     |
| P7  | delete(Kt), put(K,a)                    | Kt = a  | Kt = a   |         |
| P8  | put(Kt,b), put(K,a), put(Kt,c)          | Kt = c  | Kt = c   |         |
| P9  | put(/o/1,obj), indexed field unchanged  | entry stays | entry stays |    |
| P10 | put(/o/1,obj2), delete(/o/1), indexed   | no entry | no entry |        |

* **P4 to P8** are tested with the suffix `.txt` (the map `kvOps`) and
  with no suffix, an object key holding a String (the map `objectOps`).
* **P4, P5 in 2026.4**: the builder sorts by the keys as written, and
  `$` sorts before a digit, so the put at `Kt` is "the last put"
  whatever the order of the calls.
* **P8**: the place of `Kt` among the calls is its last call's, after
  the put at `K`.
* **P9, P10**: `/o/` has an index and `/o/1` holds an object. P9: the
  put deletes the previous value's entry and puts the same entry; it
  stays. P10: the object and its entry are gone, and `obj2`'s entry is
  not put.

So the differing cases are of two kinds:

1. **A delete after a put of one key** (B3, B6, B7, T3, T9, P6): 2026.4
   keeps the put, the new rule deletes.
2. **Two puts that key transformations make one key, called in the
   opposite order of their keys as written** (T2, T6, T7, U2, P5): 2026.4
   keeps the put whose key as written sorts last, the new rule the put
   called last.


## 5. Questions for Frans

Each has the choice made here, so that the work does not wait.

* **QL1. One key "as written" first (R1), then the final key (R2)?**
  The other reading: every call is kept until the commit, and the last
  call on each final key wins. They differ only when a key as written
  gets a put with a key transformation and another call (T9: the other
  reading gives `k` = 1). Chosen: R1 then R2. A builder cannot know a
  final key; the Pub API works this way since 015-40 (a delete of
  `/t/${transactionTime}.txt` after a put of it takes the put away,
  `Connection.setEnableKeyReplace`: "A delete's key is taken as
  written"); and a `Trans` holds one KV a key as written, however many
  calls were made.
* **QL2. "Last" among KVs that transformations make one key is the
  order of the calls**, not the order of the keys as written (2026.4)?
  Chosen: the calls. It is what "the last operation" says, and what the
  coordinator's brief names ("the order of the original operations").
  It costs a call number in each `Kv`, an int: by the object's layout
  a `Kv` is 32 bytes where it was 24 with the compact object headers
  that F53's JDK 27 uses by default (8 + 4 references), and 32 as before
  with 12-byte headers. A `Kv` lives for its transaction only, so MEM,
  the heap bytes of a stored KV, does not count it (level1.sh's MEM:
  section 9). And it costs the Pub maps' call order.
* **QL3. The Pub layer keeps the order of the user's calls** for keys
  that key replace makes one (R6; P5, P6)? Chosen: yes, by maps that
  keep insertion order. Without it the winner is the hash maps'
  iteration order.
* **QL4. The changed expected values** (section 7) need Frans's
  approval: a commit of their own on the branch.
* **QL5. A finding beside the rule (section 11, F1):** two operations at
  object keys that key replace makes one key can leave a stale index
  entry, of the operation that lost: stored, given by no scan. In
  2026.4 for two puts; with the new rule also for a put and then a
  delete. It needs the transaction's time before the commit. Not fixed
  here. Chosen: leave it to an entry of its own, if at all; section 11
  has a way to refuse such a transaction before the commit.


## 6. The implementation

On the branch, commit `0b9c9621` (9 files, 372 lines added, 46 removed,
of which the tests are about 300 lines):

* **`Kv.call`**, new, package-private: the number of the builder's call
  that made the KV. Set by `build()`.
* **`Trans.Builder.build`**: numbers the calls and puts each in the
  `TreeMap` by its key as written; a later call replaces an earlier one
  (R1). The three lines that put a put back over a later delete are
  gone.
* **`Db.sortByKey`**: the comparator sorts by key, then by `Kv.call`;
  of each run of one key the last is kept (R2). The test "a put, or a
  delete after a delete" is gone.
* **`RwEnvironmentImp`**: `kvOps`, `objectOps` and `indexOps` are
  `LinkedHashMap`s, and `writeObject` removes the key before it puts
  (as `setKv` does since 015-40), so `createTrans` gives the builder
  the operations in the order of the user's calls (R6).
* **Javadoc**: `Trans.Builder` (the class comment, `delete(byte[])`,
  `build()`), `Db.sortByKey` and the comment in `Db.putKvs`,
  `KeyTransformation.transform`, `Kv.call`, `RwEnvironmentImp`'s field
  comment, `setKv` and `deleteIndexEntry`. The Pub API's Javadoc
  (`WBuilder`, `RwEnvironment`) says "the last one counts" already and
  is not changed; `Connection.setEnableKeyReplace` gets one sentence: a
  put or a delete at the key that the replace gives is at that one key
  too.
* **`docs/levels.md` and `docs/sis-model.md`** do not state the old
  rule (sis-model.md, section 11: "a transaction's KVs reach the tree
  in key order, one a key, after its key transformations", which
  holds), so they are not changed. The Lean model has no builder.
* **UnlinkFuzz's `dup` mode** (a tool; `dup` is 0 by default) keeps the
  last operation of a key where it kept the put, so that it does what
  `Db.putKvs` does. A seed run with `dup` > 0 gives other operations
  than before.

Not changed: `Db.putKvs` but for a comment; the record, the rerun, the
write hashes (`Trans.writeKeyHashes` holds every KV's, a dropped KV's
being its kept KV's), `Db.checkSize` and `Db.checkDirtyNodes` (they
count every KV, an over-count, as before).

Mutations, each built and run against the three new tests, then put
back:

| Mutation                                   | Fails                              |
|---|---|
| M1: the three maps are `HashMap`s          | P4, P6, P8, both suffixes          |
| M2: `writeObject` does not remove the key  | P8 with no suffix                  |
| M3: `sortByKey` does not compare the calls | T2, T4, T6, T7, U2, P5, P7         |
| M4: `build()` does not number the calls    | T2, T4, T6, T7, U2, P5, P7         |


## 7. Tests

**New**, in commit `0b9c9621`; each names every wrong row in its
failure:

* `DbTesterDelete.testLastOperationWins`: rows B1 to B7 and T1 to T10,
  each a transaction of its own in one database, on a key `/c/rN` that
  held "old", as did `/c/$rN`, a key as written. Checked: the value at
  the key and at the key as written, after the transaction and after a
  restart, at startup distances 10 bytes and 10 MB; the stream, byte
  for byte that of a second database given the kept operations alone;
  T10's value transformations ran 0 and 1 times.
* `DbTesterDelete.testReusedTransLastCallWins`: rows U1 and U2; a
  `Trans` run three times (collision, none, collision), then a restart.
* `PubTester.testLastOperationWinsRows`: rows P1 to P10, through
  `WBuilder`. A `TestClock` that stands still makes each transaction's
  time the one before plus one, so the test knows the replaced key; it
  asserts the time.

On `main`'s production code (the new tests with `Db`, `Kv`, `Trans`,
`KeyTransformation` and `RwEnvironmentImp` of `1d5b18fa`), 07:22:

* `testLastOperationWins`: "34 wrong": B3, B6, B7, T2, T3, T6, T7 (`k`)
  and T9 (`$k`), in each of the four checks (two distances, before and
  after the restart), and the stream at both distances. The other rows
  hold.
* `testReusedTransLastCallWins`: "3 wrong", U2 in runs 1 and 3.
* `testLastOperationWinsRows`: P5 and P6, each with both suffixes.

So exactly the rows marked "Differs" in section 4 fail on `main`.

**Expected values changed on purpose**, in a commit of their own,
`3fc470c6` (QL4, for Frans's approval). With commit `0b9c9621` alone the
full unit suite (1,648 tests) fails in these two tests and no other;
with `3fc470c6` all 1,648 pass (07:29):

* `DbTesterJavadoc.testTransBuilderOneOperationPerKey`: key "a" (put,
  then delete): "1" becomes no value. Key "f" (put, delete, put,
  delete): "2" becomes no value. Keys "b" to "e" as before.
* `DbTesterDelete.testOneOperationAKeyAfterTransformations`: key "/c/b"
  (a transformed put, then a delete): "b1" becomes no value; the twin
  database, which gets the kept operations alone, gets a delete of
  "/c/b" where it got a put of "b1". Keys a, c, d, e as before. Its
  assert of a value takes the class's `assertValue`, which allows no
  value.

Not changed, though it names the rule:
`DbTester.testTransformedKeysSorted` (its plain put of a transformed key
is called last and sorts last: kept by both rules).


## 8. The stream's bytes

* **Without repeated keys: the same bytes.** StreamDigest `all` (12
  configurations of level2.sh's and level3.sh's RestartInvariance, four
  modes each, one operation a key in every transaction), 07:30: `main`'s
  jar (`1d5b18fa`, built in a worktree) against the branch's
  (`3fc470c6`), both run with `main`'s compiled StreamDigest, then
  `compare`: "DIGESTS IDENTICAL (48 of 48; of the identical, the
  physical cut differs in 0)". By the code: `build()` keeps every KV of
  such a transaction in the same `TreeMap` order, and `sortByKey` drops
  none.
* **The Pub layer, without repeated keys: the same bytes.** The change
  of map (R6) changes only the order in which `createTrans` calls the
  builder, which sorts. Checked by a probe (not committed; a Pub
  database on a `MemoryStream` with a `TestClock`): 3,000 transactions
  of 1 to 12 operations on distinct keys, through `w()` and `rw()` in
  turn: Strings at keys with a suffix, objects in a directory with an
  index, deletes, and key replace at both kinds of key; seeds 1, 2 and
  3 (19,638, 19,475 and 19,100 operations; streams of 2,707,096,
  2,679,496 and 2,644,192 bytes). `main`'s build and the branch's write
  the same stream but for 16 bytes at offset 24 of each of the 14 meta
  blocks, the database's id, which is random: two runs of one build
  differ there too.
* **With repeated keys**: the record is that of the kept operations
  alone, byte for byte (`testLastOperationWins`, both distances). So a
  transaction's bytes differ from 2026.4's exactly where the kept
  operation does: a delete where there was a put (the record holds no
  value node for the key), or the other put's value. On `main`'s code
  the test's stream of the 17 rows is 11,696 bytes against 11,968 for
  the new rule's kept operations at a startup distance of 10 bytes, and
  3,824 against 3,800 at 10 MB.
* **No record format change**: the record holds the KVs kept, and the
  rerun applies them in stored order (024-02, section 8.4; Q5: "A
  writer's rule: no reader changes").


## 9. Gates

On the branch's head `3fc470c6`, in the clone, with the heavy-run lock:

| Gate                          | When           | Result                                   |
|---|---|---|
| The unit suite                | 07:29          | SUCCESS, 1,648 tests in 39.1 s           |
| StreamDigest `all`, compare   | 07:30          | DIGESTS IDENTICAL (48 of 48), section 8  |
| The Pub stream probe, 3 seeds | 07:33          | the same but for the database's id       |
| `java/before-commit.sh`       | 07:30 to 07:34 | BEFORE COMMIT OK (262 s)                 |
| `java/stress/level1.sh`, full | 07:35 to 07:37 | LEVEL 1 OK, MEM 129, SS 1.51             |
| `java/stress/level2.sh`, full | 07:37 to 07:48 | LEVEL 2 OK, 70 traces TRACECHECK OK      |

* **before-commit.sh**: deps 9 packages, doubles 7 packages, unit 1,648
  tests in 42.8 s, f 89 tests in 68.3 s, demos OK (14 runs). Of its
  262 s about 180 s are `doubles.py`: section 11, F2, on `main` too.
* **level1.sh**: unit; DagFuzz 300 rounds at each node size, 0
  failures; DeleteRepro; RestartStress, 0 failures in each of its 12
  configurations; RestartInvariance: "STREAM: identical", no checkpoint
  differs or violates; Props: MEM 129 (at most 131), SS 1.51 (at most
  1.52). So the call number in `Kv` does not show in MEM.
* **level2.sh** was run because the change is in the path of every
  transaction, the conformance traces' too (`Trans.Builder.build`,
  `Db.sortByKey`), though their transactions name no key twice. Unit;
  RestartStress, 0 failures in its 13 configurations; RestartInvariance,
  "stream identical, all checks OK" in its 8; CrashTest, 0 failures;
  BryanRepro, 40 cycles, 0 failures; A2A3Check2 OK on 3,000, 500 and
  6,000 transactions, 0 adoptions below the old parent; "conformance:
  traces: 70, TRACECHECK OK: 70".
* **Not run**: level3.sh, level4.sh, night.sh (the brief asks for none
  of them; reclaim and eviction are not touched).


## 10. What C must change later

BergDB's C clone (022) follows a release, not `main`; nothing in C is
changed here. When C is taken to release 2026.5:

* **`tr_build`** (`c/src/trans.c`, "then each key's last pair, but a
  delete never replaces a put"): of the pairs of one key, keep the last
  one; the three lines that put the put back go, as in Java. The
  header's comment (`c/src/trans.h`, "a delete never replaces a put")
  says the new rule.
* **The collapse after the key transformations** (Java's
  `Db.sortByKey`; C gets it with 022-02's update to 2026.4, where it is
  "the last put in the order of the keys as written"): sort by key,
  then by the pair's call number, and keep the last of each run. In C a
  built transaction points to the builder's pairs, which are in the
  order of the calls, so a pair's index in `b->kvs` is its call number:
  no new field.
* **Tests**: `c/test/unit/t_db.c` ("a delete after a put: the put")
  expects the old rule; the ports of
  `testTransBuilderOneOperationPerKey` and
  `testOneOperationAKeyAfterTransformations`, if 022-05 ported them,
  change as section 7 says; the new tests' rows B and T are worth
  porting.
* **The cross tests** compare C's and Java's streams byte for byte: a
  Core transaction with a put and then a delete of one key writes other
  bytes under the new rule, so C and Java must change together for
  such a workload (`JAVA_REF`). A workload with one operation a key is
  not touched.
* **No change** of the record format, the reader or the rerun.


## 11. Findings beside the rule

* **F1. Operations at object keys that key replace makes one key can
  leave a stale index entry.** The index entries of a transaction are
  worked out before the commit from each object key as written (020-10,
  section 5.1), and the Pub layer cannot see that two keys become one:
  the time is known at the commit. A stale entry is a stored KV that no
  scan gives (a scan skips an entry that its value does not have,
  020-10, section 3.4), so no answer is wrong; it is storage that
  nothing takes back. Seen by a probe (not committed) on `main`'s build
  and on the branch's: a directory `/o/` with an index, `K` =
  `/o/${transactionTime}`, `Kt` the key with the time's digits, holding
  an object of value 5; the objects put have values 7 and 8:

  | Calls               | `main`: Kt, entries stored | Branch: Kt, entries stored |
  |---|---|---|
  | put(K,7), put(Kt,8) | 8; 2, one stale            | 8; 2, one stale            |
  | put(Kt,8), put(K,7) | 8; 2, one stale            | 7; 2, one stale            |
  | put(K,7), delete(Kt) | 7; 1                      | nothing; 1, stale          |
  | delete(Kt), put(K,7) | 7; 1                      | 7; 1                       |

  Every scan of the index gave what `Kt` holds, in all eight runs. So
  the two puts leave a stale entry in 2026.4 as with the new rule; the
  put and then the delete leaves one with the new rule only. It needs
  the transaction's time before the commit: a guess, a clock that
  stands still, or a `TestClock`. A way to close it: refuse, at the
  call, an operation at an object key when the transaction also holds a
  replaced put whose key it could become (the same key with 18 digits
  where `${transactionTime}` is), and the other way round; checked in
  `RwEnvironmentImp` before the commit, an `IllegalArgumentException`
  as 020-14's. Not done here.
* **F2. `java/doubles.py` takes 3 minutes, on `main` too.** Run alone
  (`python3 -I doubles.py`), 07:38 to 07:44: 181.8 s of CPU in the
  clone, 180.8 s in the worktree of `main` at `1d5b18fa`; the header of
  before-commit.sh says "under a second". So before-commit.sh takes
  about 4.5 minutes where it took 2 (262 s here; 023-09, section 7.3,
  has 283 s). Not caused by this branch, not fixed here. Where the time
  goes, by a timer around `doubles.check` for each file, on `main`
  (07:44 to 07:47): 176.9 of 183.0 s in `core/Db.java`, 4.0 s in
  `storage/BufferedStream.java`, 1.1 s in `common/StringUtil.java`, the
  other 180 files about a second together. Which of its regular
  expressions is slow on `Db.java` was not looked for; `method_regions`
  runs one with nested repeats for each guarded name.
* **A reused `Trans` keeps its transformed keys** (old, not changed): a
  key transformation sets the KV's key (`Kv.setKey`), so the next run's
  transformation gets the key the last run left, not the key as
  written. The Pub layer builds a new `Trans` for each run
  (`createTrans`), with the keys as written.


## 12. Log

2026-11-11, 07:10. Started, by an agent of coord-1111 ("low"). Read:
the common brief, 024's readme, 024-04, 015-40, 023-08 (sections 5 to
7), 023-09 (sections 7 and 8), 024-01 (CA1), 024-02 (Q5, section 8.4),
and the code: `Trans`, `Trans.Builder`, `Kv`, `KeyTransformation`,
`Db.putKvs`, `Db.sortByKey`, `RwEnvironmentImp` (`kvOps`, `objectOps`,
`indexOps`, `indexEntries`, `createTrans`, the key replace
transformation), the tests of 015-40's rule, UnlinkFuzz's `dup` mode,
the C clone's `tr_build` (022's `c/src/trans.c`).

2026-11-11, 07:14. Sections 1 to 5 written, before any code.

2026-11-11, 07:19 to 07:25. The three new tests, run on `main`'s code
(the differing rows fail, the others hold); the change; the mutations
M1 to M4; the full unit suite (two existing tests fail, as read
beforehand); the first commit (`0b9c9621` after two amends: its
message's form, and one sentence in `Connection`'s Javadoc); the two
tests' expected values changed.

2026-11-11, 07:25. **A mistake of mine:** from 07:21:11 to about
07:25:30 I built (about 8 times, 6 s each at about 3.5 cores) and ran
unit tests, among them the full unit suite once (about 45 s), while the
heavy-run lock's owner file said "touch timing: the last touch before
the fix, 1M and 10M keys 07:21:11". The common brief forbids even small
compiles then. The agent "touch" may have measured slow or noisy
figures in that window. Told to the coordinator at 07:26 (the agent
"touch" could not be reached by name). Since then nothing is run while
the owner file says "timing"; a background command waits for the lock.

2026-11-11, 07:28 to 07:37, with the heavy-run lock (07:28:41 to
07:37:44): the unit suite on both commits, commit `3fc470c6`,
StreamDigest, the two probes (F1 and the Pub stream),
before-commit.sh, level1.sh; the results are in sections 7 to 9 and 11.
07:37:51 to 07:48:34: the lock again, for level2.sh full: LEVEL 2 OK.
Beside it, `doubles.py` timed (F2).


## 13. State

2026-11-11, 07:49, by an agent of coord-1111 ("low"). The work of the
brief is done; the branch waits for Frans's answers and the
coordinator's landing.

* **Done.** The rule (section 3), the table (section 4), the questions
  with the choices made (section 5); the change and the new tests,
  commit `0b9c9621`, and the two existing tests' expected values,
  commit `3fc470c6` (sections 6 and 7); the stream's bytes (section 8);
  before-commit.sh, level1.sh and level2.sh on `3fc470c6`, all OK
  (section 9); what C must change (section 10); F1 seen by a probe and
  F2 measured (section 11).
* **Not done.** Nothing of the brief. Not asked for and not done: a fix
  of F1 or F2; level3.sh and level4.sh; the C clone; 024's readme
  (its line for this file and its log are the coordinator's).
* **For Frans.** QL1 to QL5 (section 5); QL4 first: the two changed
  expected values of commit `3fc470c6`.
* **For the coordinator.** My builds and tests during "touch"'s timing
  run, 07:21 to 07:25 (the log); F2, before-commit.sh's 3 minutes in
  `doubles.py` on `main`.
* **Where.** Clone `/Users/f/fl/bench/2026-11-11/low/clone`, branch
  `024-10-last-operation-wins`, from `main` at `1d5b18fa`, head
  `3fc470c6`, two commits, the working tree clean; nothing pushed. A
  worktree of `main` for the byte comparison, built:
  `/Users/f/fl/bench/2026-11-11/low/base`. The probes (F1Probe.java,
  PubDigest.java; run with `-cp out:java/build/classes`, as the jar is
  sealed) and StreamDigest's two outputs:
  `/Users/f/fl/bench/2026-11-11/low/probes/`. The gates' logs: the
  clone's `java/build/before-commit/`, `level1/` and `level2/`.
* **To continue.** To land: the branch's two commits on `main` (the
  coordinator), after Frans's word on QL4; if `main` has moved in
  `Trans.java`, `Db.java` (`sortByKey`), `Kv.java`,
  `RwEnvironmentImp.java` or the two testers, rebase and run
  before-commit.sh again. If Frans chooses the other reading of QL1 or
  QL2: QL2's is `Db.sortByKey`'s comparator and the rows T2, T6, T7,
  U2, P5; QL1's needs the builder to keep every call until the commit.
  The heavy-run lock is not held by this work.

2026-11-13. Status set after the release (coord-1113).
