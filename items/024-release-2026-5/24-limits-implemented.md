# 024-24. The limits, implemented

Created 2026-11-11 by Frans Lundberg. Status: done (2026-11-11): on
`main` since `87afef86`, the night's fix since `9dd763df`. Q2 accepted
by the coordinator under Frans's delegation (024-28, section 8); Q1 not
answered.

The limits that Frans decided for release 2026.5 (024-17, section 8),
built into the Lean model, the Java code, the tests and the documents,
and gated. By the agent "lim3" of coord-1111, from 17:49.

Frans, 2026-11-11, 17:41 (024-17, section 8): "I want be a bit more
conservative, possibly increasing in a future version. So, use: L1 =
500, L2 = 111, L4 = 8 MiB, L5 = 32 MiB. The rest as recommended."
With 024-17's restatement of 17:45: L3 = 56 KiB, L6 = 111 with a
refused put (QL4), QL5, QL6, QL7, QL8 (a). Not here: CRC32C (QL9,
024-25), reclaim's large-value step (QL10, documented only), the C
clone (022, which matches release 2026.4; its `cbench` keeps batches
of 1,000).


## 1. The Lean model

Commit `1d600ea1`, `lean/SIS/Tree/Bound.lean`:

* **`Limits`** gains a third field, `maxTxSegs`, the segments of all
  keys of a transaction (from L3: k bytes of keys in n keys are at most
  k / 7 + n segments), by default `maxOps * maxSegs`. `Tx.within`
  checks the sum too.
* **`Limits.release`**: 500 operations, 8,692 segments a transaction
  (57,344 / 7 + 500), and a key as long as L3 allows, since BergDB's own
  keys pass L2; **`Limits.user`**: 500 operations of 16 segments
  (111 bytes).
* **`Params.nodesALevel`**, the count with q (024-17, 5.2 and 5.2a):
  5 + ceil(2 (q + 2) / (q - 1)), one more at q = 2 for the root
  collapses: 14, 9, 8 and 8 at node sizes 8, 14, 30 and 62 (checked by
  `#eval` on `Params.java`).
* **`Limits.dirtyNodes`** for record format 7 is now a sum over
  segments: `nodesALevel x (H + 2) x segments + 14 x maxOps`, with
  segments = min(`maxTxSegs`, `maxOps x maxSegs`); 2026.4's writer
  keeps 8 a level and 2 an operation, in the same sum form. Option 2's
  term (024-23) is covered: a node compacted at most once overflows at
  least once, within the 2 + k / q a level of the count.
* **TP26** (`DirtyBoundFromLimits`) as before, a statement over the new
  count; `treetest` (`TreeTest.lean`) and `treecheck` (C-T8,
  `Check/Tree.lean`) check it on every transaction with the
  transaction's own operations, longest key and sum of segments. TP23
  is unchanged.
* **`ReleaseFits M H`**, proved by `decide` (no axioms): the nodes of
  `Limits.release` at their largest size and the two top nodes fit 15/16
  of 2^31 - 9 at node sizes 8, 14, 30 and 62 with H = 61, 38, 22 and 16
  (7,673,344; 3,136,120; 1,675,864; 1,258,648 nodes, as 024-17's 5.3).
  `twentyALevelDoesNotFit30`: the count of before, 20 a level, does not
  fit 500 operations of 111 bytes at node size 30 and H = 22.

`lake build`: OK (183 jobs). No `sorry`; `#print axioms` of the new
theorems: none.


## 2. The Java checks

Commit `aaa0e881` (with `IndexReference`'s constant):

* **Constants** in `Db`: `MAX_OPERATIONS` 500 (L1), `MAX_KEY_BYTES` 111
  (L2), `MAX_TRANS_KEY_BYTES` 57,344 (L3), `MAX_VALUE_BYTES` 8,388,608
  (L4), `MAX_TRANS_BYTES` 33,554,432 (L5), each with its Javadoc; `Db`'s
  class Javadoc has "Limits", and "Keys and values" no longer says that
  a key has no maximum length. `IndexKeys.MAX_LEVEL_BYTES` (L6) is
  `Db.MAX_KEY_BYTES`.
* **L2 and L4 at the call.** Every `Trans.Builder` call that takes a key
  (put and delete, of `byte[]`, `String` and `long[]`, the put with
  transformations) refuses one over 111 bytes as stored, "The key has N
  bytes, more than 111 (bergdb 024-17, L2)."; every put refuses a value
  over 8 MiB, "The value has N bytes, more than 8388608 (bergdb 024-17,
  L4). ...", both with `IllegalArgumentException`, nothing added.
  `keyRead()` is not checked (a read).
* **BergDB's own keys**: `Trans.Builder.putLongKey()` and
  `deleteLongKey()`, internal, take a key over L2 only under "/#" (01
  25), do not check a value's length, and mark the KV (`Kv.longKey`)
  (since the review's R1 and R2, section 7; `aaa0e881` checked L4 in
  `putLongKey` and took any long key). Used by the Pub layer's commit (`createTrans`: its
  `kvOps`, where a build step's entries are, and `indexOps`), by
  `IndexManager` (definitions, markers, the cleanup's deletes: an index
  name has up to 255 bytes) and by reclaim's step (a live key may be an
  entry; a check that threw there, inside a user transaction's go point,
  would fail the database).
* **L1, L3, L5** in `Db.checkLimits`, called by `checkSize` before the
  write lock, for user transactions only (reclaim's are within them by
  construction, 024-17, 5.5): the KVs after the builder's rule of one a
  key, their keys' bytes, and keys and values; `DbException` "The
  transaction has N operations, more than 500 (bergdb 024-17, L1).
  Split it into transactions." and likewise for L3 and L5.
* **A key transformation's keys** (`Db.transformKeys`): a transformed
  key over L2 (but a long-key KV's) or the keys over L3 refuse the
  transaction with `DbException`, after which the KVs, hashes, time and
  clock are given back as for 024-16's refusal (`giveBack`, shared).
* **QL6**: a value transformation's result over L4 (in `putKvs`, after
  the go point) throws, so the database fails, for user transactions;
  `ValueTransformation`'s Javadoc keeps 015-51's rule.
* **The Pub layer**: `RwEnvironmentImp.checkKeyBytes` at put and delete
  (the ikey's UTF-8: "/a/b" is "/da/-b", so each "/" counts two; key
  replace keeps a key's length, so the template is checked exactly);
  `checkValueBytes` before a `byte[]` is copied, a `String` through
  `stringValue(s, MAX_VALUE_BYTES)`, an object through
  `DataObjects.toDbObject(x, MAX_VALUE_BYTES)` (021-23's count, the
  place named), a `DbObject` by its bytes. `DbObject.toDbObject()` alone
  keeps 2^31 - 9.
* **L6 / QL4**: `IndexDefinition.entryForPut` refuses a put whose levels
  pass 111 bytes ("... has more than 111 bytes of encoded levels for the
  index "n" (bergdb 024-17, L6) ..."); a build over values put before
  the index still gives them no entry (`entry()`), as 4,096 did.
* **QL7**: `NodeStream.readRecordHeader` reads the size, refuses one
  over `MAX_RECORD_SIZE` (L7) as corrupt, checks it against the stream,
  then reads the last byte and, for a committed record, the format byte:
  another format is refused with `VersioningStreamException` before the
  record is read. Used by `readTransBytes` and the iterator. An
  uncommitted record (a crash's tail) is skipped as before.
* **QL5**: the checks of 005-17 and 005-31 are unchanged, refusals.
* **Javadoc**: `Db`, `Trans.Builder`, the `pub` package's "Limits" (a
  new section of "The rules in full"), `Connection` ("Keys", put's
  `DbException`), `WBuilder.execute`.


## 3. Tests and programs that changed

Each its own commit on the branch (Frans's approval needed for the
changed expected values; the claims of each test are kept unless said):

| Commit     | What                                                                 |
|------------|----------------------------------------------------------------------|
| `39ed1c74` | CapacityTester.testWarmupDoesNotWait: 500 puts (were 1,000)          |
| `b7283071` | KeyFactory.crazyKey: keys of 20 to 111 bytes (4 crazy-key tests)     |
| `ced8c219` | DbTesterDelete: 500 a transaction; a 108-char key (was 303)          |
| `179412ef` | DbTesterGetMany.testEndKeyPassesNoDeletedLongKeys: batches of 500    |
| `3c9f7f8c` | DbTesterJavadoc.testKeysAndValues: a key of 111 (was 3,000), 112 out |
| `c303944c` | DbTesterLongKeys rewritten at L2 and L3, every node size             |
| `18b7abe5` | Eviction.testHistoricalParentsAndLongKeys: keys of 111 (were 302)    |
| `5182cc8f` | LimitsTester: keys to 111 and 112 refused; L1 at 500 and 501         |
| `6f1c5a9b` | DataObjectsTester.testPutTooLarge: a put refused at 8 MiB            |
| `68098d6c` | IndexDefinitionTester: L6 = 111 (was 4,096)                          |
| `c676b56b` | IndexReference.testFunctionSizeLimit: 111; tooLong()                 |
| `71b40e6b` | IndexHarness: long strings near 111; a refused put checked           |
| `b6b8e563` | FormatFuzzer: levels near 111; an L6 refusal expected                |
| `325d9590` | PubTesterIndexJobs.testLargeValueNoEntry: the put refused (QL4)      |
| `454b46ca` | PubTesterIndex: three tests in two w() each                          |
| `5f9a5c89` | PubTesterLongKeys rewritten at L2 (111 bytes, 34 deep, å)            |
| `1b900ca2` | PubTesterPrimary.testListingBeforeDeletedKeys: w() of 500            |
| `1d89f1c5` | PubTesterThreads: w() of 500; 20 rounds of 500                       |
| `beeee6fe` | DbTester.testTooManyDirtyNodes (f): every 20th key, 500              |
| `f60b7f37` | DbTesterStream.testLargeTransaction (f): 8 MiB (was 20 MB)           |
| `f95acb7b` | Crazy (f): 8 MiB value, a key of 111 (were 20 MB, 10,000)            |
| `71c63ff2` | BigDb, BigDbWithDeletes (f, perf): values at most 8 MiB              |
| `e13a9c0b` | Get, PerfGetMany (perf): batches of 500 (were 10,000)                |
| `efb6ac08` | PayDemo (before-commit), PayTest (night): 500 a w() (were 1,000)     |
| `250d0f4b` | LargerThanMemory (level 4), ObjectBench, PauseProbe: 500             |
| `2c660d16` | Perf.java, Soak: longlen 111 (was 120); performance.suite's note     |

* **Results that stop being comparable**: `performance.sh`'s long-key
  results (read-100, read-1k, read-10k, read-quick, read-s; gets, scans,
  the mixed phase) with every earlier run, 2026.4's reference included:
  16 segments a key, not 18. And where the batch size shows (bytes a
  put, time a commit) in PayDemo, PayTest, LargerThanMemory and the perf
  group.
* **New tests** (`4fbb965e`): `DbTesterLimits`, for each limit the value
  at it taken and one step over refused, nothing written, the database
  going on (L1 500/501; L2 at every call, two-byte letters, and by a key
  transformation; L3 57,344/57,345 through `putLongKey`; L4 8 MiB and a
  byte at every put call; L5 32 MiB and a byte; QL6 a transformation's
  result over L4 fails the database, the restart has the state before);
  `NodeStreamTester.testRecordHeaderFirst` (QL7); and inside the
  rewritten tests, L2 at every node size (DbTesterLongKeys), the Pub's
  wording (PubTesterLongKeys: 54 å taken, 55 refused), L6 at the put
  (PubTesterIndexJobs, IndexDefinitionTester).


## 4. Documents

`4a9ebcb2`: `docs/levels.md` section 3 (the limits, where each is
checked, the bound with q and what is proved), `releases/next.md`
(a section "Limits", with the users' wording and the tools whose
results stop being comparable).


## 5. Decisions taken here

* **Internal calls skip L4 too**, not only L2: reclaim copies values
  that a user put within L4, and a refusal inside its step would fail
  the database; the Pub layer checks L4 itself at the put. So the
  internal calls check no value's size, and `Db.execute` checks each KV
  (L2 but for BergDB's own keys, L4), L1, L3 and L5 on a user
  transaction (since the review's R1, section 7).
* **A build over values with levels over L6 gives no entry**, as over
  4,096 before: the values were put before the index existed; a failed
  build would be worse. Question Q1 below.
* **The reader's format check** reads the last byte first, so that an
  uncommitted tail is skipped as before (the corrupt-stream tests found
  that a format check alone refused a crash's tail).
* **`cbench`** (the C clone's) is not changed: the clone matches 2026.4
  and has no limits (022).


## 6. Questions for Frans

* **Q1. A build over an object with levels over 111 bytes**: no entry
  (as now), or fail the build? Recommended: no entry, documented (the
  `pub` package's "Limits" says so).
* **Q2. The changed tests** of section 3: approve them as a set.
  Recommended: yes; none weakens a claim but "in one transaction" at
  2,000 keys (DbTesterDelete, DbTesterGetMany, PubTesterPrimary), which
  L1 forbids.


## 7. The review (rev24) and its fixes

The review (`24-limits-implemented/review.md`, 19:04): land with fixes.
Fixed as new commits on the branch, 19:05 to 19:09:

* **R1** (`a0851275`): `putLongKey` checks a value for null only, as its
  Javadoc says (it checked L4, and reclaim's copy of a value over L4,
  put through the public `Trans.kvs`, failed the database: the review's
  probe). `Db.checkLimits` now checks each KV of a user transaction,
  whatever built it: a value over L4, and a key over L2 unless one of
  BergDB's own from the internal calls, refused with `DbException`.
  Test: `DbTesterLimits.testEachKvChecked` (the probe, then 20,000 puts
  with reclaim running).
* **R2** (`a0851275`): `putLongKey`/`deleteLongKey` take a key over L2
  only under BergDB's prefix "/#" (the bytes 01 25), at the call
  (`IllegalArgumentException`) and in `checkLimits`; so a Core user
  cannot put a long key through them. Every key BergDB puts over L2 is
  under "/#i/". Test: the same.
* **R3** (`e3e56207`): Db's Javadoc and `docs/levels.md` no
  longer say that a transaction within the limits never meets 005-31:
  `Db.checkDirtyNodes` counts a KV with a key transformation as
  (20 or 3) x height x segments + 3 from the stream's length, and one
  with a value transformation as a put and a delete, so 500 such KVs of
  111-byte keys at node size 62 are refused on a stream of 258 kB (the
  review's probe). **QL5's step to a `Bug` for 005-31 needs a count of
  transformed KVs within the model's bound first** (to be added to
  024-17's QL5; this item writes only its own file).
* **R4, R5** (`e3e56207`): `WBuilder.put`, `Connection.put` and
  `delete`, `RwEnvironment.put` and `delete` name L2 and L4;
  `WBuilder.execute`, `Connection.put` and `rw` name L6's
  `IllegalArgumentException`; `IndexBuilder`'s rule says 111 bytes and
  the refused put; the pub package's "Limits" and `releases/next.md`:
  L3 counts all the keys of a transaction.
* **R7** (`c31d7996`): `DbTesterLongKeys.testOwnLongKeysSmallStack`
  reaches 021-16's depth again: BergDB's own keys of 10,000 and 57,344
  bytes (8,193 segments) put and started again in a thread with a stack
  of 256 kB, the record limit at 30 MB so that `execute()`'s cheap count
  fails and `Dag.dirtyNodeBound` walks the new key (`freshTreeBound`):
  cheap count 3 x 13 x 8,193 + 3 = 319,530 nodes against about 51,700
  that fit. Not reached any more: a user key past 111 bytes, and the
  Pub API's deep keys (20,000 directories); the Dag below the checks
  keeps 400 kB (`DagTester.testLongKeyWalks`).
* **R12** (`d0b52eaa`): `DbTesterDelete.testDeleteEveryKey` also at 500
  keys, deleted in one transaction.
* **Notes, not changed:** R6 (no limit on the indexes of a directory:
  with k >= 250 on update, every object put there is refused by L1, and
  with long names and levels by L3 from k = 58; its message says "split"
  where a single put cannot; a limit at index creation is for later);
  R8 (LimitsTester reaches 005-31 less often, 8 refusals against 37 on
  base in 12 seeds, still reached; n of 300 to 500 more often is a later
  change); R9 (IndexHarness checks an L6 refusal's cause, not a put that
  should have been refused; FormatFuzzer's expectation calls
  `entryForPut` itself; the boundary is tested apart); R10 (L7 is not a
  consequence of L1 to L5 with value transformations: their results up
  to L4 each are not in L5; QL5 for 005-17 needs them counted too);
  R11 (`testRecordHeaderFirst` does not show that no buffer of the
  record's size is made first; a stub stream of about 2^31 bytes would).


**024-25 merged** (19:23, `c87aa6f9`, main `3dd38b23`, CRC32C): no
conflict. Its review's R5 (rev25), fixed in `b0d41461`: a top node is
now 48 + 16 h bytes, h at most 48 (`TopNode.MAX_HEIGHT`), so
`Db.checkDirtyNodes`' `topBytes` and the Lean `ReleaseFits` count
2 x (48 + 16 x 48 + 16) bytes, exactly (were 2 x (40 + 16 x 64 + 16),
the size before CRC32C, which bounded it). A key node's bytes are
unchanged (32 + 16 x size). `ReleaseFits`' doc now says that it makes
005-31 unreachable for transactions without transformations (R3).


## 8. Gates

* **On `4a9ebcb2`** (before the review): Lean (lake build, no sorry or
  axiom, test-traces) OK; treetest's default set OK (17:52 to 18:50, 57
  minutes on one core: the slot held past the 40 minutes of the day's
  rule); before-commit OK (111 s); level1 OK (194 s); unlinkfuzz OK
  (3,226 rounds, 330 s); level2 stopped at 19:09 for the fixes. Logs in
  `lim3/logs-98454653/`.
* **On `d0b52eaa`** (rev24's fixes): Lean OK, before-commit OK (102 s),
  level1 OK (184 s), unlinkfuzz OK (330 s); level2 from 19:20 (logs in
  `lim3/logs-26e19264/`). Then main (024-25) merged.
* **On `b0d41461`** (main `3dd38b23` merged, rev25's R5), the final
  head, by `lim3/gates-merged.sh`, one slot at a time, 19:33 to 20:18,
  all rc = 0 (logs in `lim3/logs/`, summary `lim3/gates.out`):

| Gate                                            | Result, time              |
|-------------------------------------------------|---------------------------|
| lake build, no sorry or axiom, test-traces      | OK, 13 s                  |
| before-commit                                   | BEFORE COMMIT OK, 82 s    |
| level1 full                                     | LEVEL 1 OK, 138 s         |
| unlinkfuzz                                      | OK, 3,226 rounds, 292 s   |
| level2 full (treeconf small, drain, reclaim)    | LEVEL 2 OK, 764 s         |
| conformance small, drain                        | OK, 26 s, 29 s            |
| level3 full                                     | LEVEL 3 OK, 445 s         |
| conformance medium, reclaim, evict              | OK, 141 s, 150 s, 63 s    |
| level4 full                                     | LEVEL 4 OK, 500 s         |

  treetest's default set (TREETEST OK) ran on `4a9ebcb2`; the Lean
  model's change after it is `ReleaseFits`' top node bytes only (and
  the merge brought no Lean change but 024-25's), checked by `lake
  build`'s `decide`.


## 9. Fix after the night run, 2026-11-11

By l6fix, a subagent of the day's coordinator, 22:11 to 23:08.

**The failure.** The night run on main `8664db0e` (this item landed as
`87afef86`) failed twice with the same assertion of `IndexHarness`
("refused for L6 by NAME, but no write's levels are too long"): the
night test `IndexHarness.testSeedsLong`, seed 20768001, step 296 (index
`i0`, the put of `/h/a/kå`), and `harness-soak`'s job 6 h2, `-Devict=every
-Daudit=10 IndexHarness 20261111001 2000 4 1 300 0 0 100`, step 192
(index `ä`, the put of `/h/a/k9`). Both repeat in seconds on the night's
jar.

**The cause: the product code.** The soak's case shows it. The index
`ä` has the levels `[string c, long n.a, string b]`; the put was of
`{"b": 0, "c": 56 NULs, "x.y": 0}`. Its `c` level is 56 x 2 + 1 = 113
bytes (each 00 written as two), over L6, but `n.a` is absent and `b` is
a long where the index has a string: the value has no entry at all.
`IndexDefinition.entryLevels` read the levels in order and returned the
refusal (`tooLong`) at the first level whose running size passed 111
bytes, before it looked at the later levels. 024-17's L6 (section 6.1)
limits an *indexed* value, one that has an entry, and `IndexBuilder`'s
rules (its Javadoc) give an entry only if every level's field is found
with the level's kind; the length rule comes after. The harness's
oracle (`IndexReference.tooLong`: every level found and of its kind,
then the sum over 111) says that, so the oracle was right and the code
wrong. A user saw a put refused for an index that never indexes the
value; before 024-24 such a value had no entry and was taken.

**The fix** (`IndexDefinition.entryLevels`): a level that passes L6
sets a flag `over` instead of returning; the loop goes on through the
later levels, each of which still returns "no entry" if it is absent,
of another kind or NaN; only after the loop does `over` return
`tooLong` (refused for a put, no entry for a build). A string level
after `over` is checked for its kind but not measured, so a value with
a string of a megabyte costs no more than before.

**The build path (Q1).** A build over existing objects calls
`entryLevels(ikey, value)` without the refusal (`UseIndexBuilderImp`),
where "too long" and "no entry" are both null: it had no such error
and does not change. `FormatFuzzer`'s L6 expectation calls
`entryForPut` itself on one-level indexes, where the order of levels
cannot matter.

**The test.** `IndexDefinitionTester.testFunctionLimitNoEntry`: an index
`[string c, long n.a, string b, double d]`, `c` of 56 NULs (113 bytes),
111 x's and 1 MiB of x's, with each of six values that have no entry
(`b` a long, `n.a` a string, `n` not an object, `d` absent, `d` NaN, and
the soak's own shape): `entryLevels` and `entryForPut` give null, no
refusal; with every level present the put is refused; levels over 111
only with the later string `b` are refused, and 111 bytes exactly are
taken. It fails on the code before the fix and passes after. The two
failing runs pass on the fix (seed 20768001 to step 400 in 3 s, the
soak's command in 60 s).

**Not changed.** R9 (section 7) stays: `IndexHarness` checks that a
refusal has a cause, not that every put with too long levels is
refused; `testFunctionLimitNoEntry` and `testFunctionLimit` hold the
other direction at the unit level.

**Does L6 depend on the key?** No. Two of the three L6 failures were
at `/h/.../kå`, but `entryLevels` uses the key only to see that it is
an object key (no suffix, or `.obj`) and to name it in the message;
the count is over the value's levels alone. `kå` is one of
`IndexHarness.OBJECT_NAMES`' 16 names, which `KillRestartHarness`
shares; the soak's failure was at `k9`.

Two more failures of the same night came from the limits, both in a
harness that did not know them (the coordinator added them to this
fix at 22:27):

**(a) fuzz, area starts, seed 20768010, iteration 28990**: "The key has
114 bytes, more than 111 (bergdb 024-17, L2)", thrown by
`Trans.Builder.put` in `FormatFuzzer.startsOne`. The area changes one
of BergDB's internal keys under `/#i/` (a definition's or a marker's
key, by `mutateBytes`, which may add bytes) and writes it through the
Core, then checks what a start reads. BergDB writes its own keys under
`/#` with `putLongKey`, which allows them past L2 (024-17, section 6.2 (a));
an index entry may take about 500 bytes. A start must read such keys,
so the area keeps its inputs and writes them as BergDB does:
`putLongKey` (which still refuses a long key outside `/#`). Test:
`FormatFuzzer.testFuzzStartsLongKey` runs that iteration (unit group).

**(b) kill-restart**: a child failed with an L6 refusal of a put at
`/h/d/kå` for the index `i1` (database seed 3059697745756165568, run
1). `KillRestartHarness` makes its values with `IndexHarness`'s
generators, whose `LONG_STRINGS` are since 024-24 at and around 111
bytes; a refused put threw out of the child's writer, and its journal
has no way to say "refused" (a `T` line without `C` is a transaction
in flight at the kill). The harness checks kills and restarts, and
`IndexHarness` and the unit tests check L6, so its values now stay
within L6: `KillRestartHarness.cut` cuts a string longer than 18 chars
(only the `LONG_STRINGS`, ASCII) to 18, at most 37 bytes as a level
(18 00s, each written as two, and the final 00); every other string or
byte[] of the generators takes at most 17 bytes, and `def()` makes at
most 3 levels, so a definition's levels take at most 111 bytes. Test:
`KillRestartHarness.testWithinL6` (2,000 transactions against 100
definitions with `IndexReference.tooLong`; it fails with the cut at
1,000 chars); `Pack` now lists the class, so its test runs in the unit
group (0.6 s). The kept database was gone with the night's clone, so
whether that put had an entry is not known; with (b) it does not
matter.

**Branch.** `024-24-l6fix` from main `0f4d1c47`, in
`/Users/f/fl/bench/2026-11-11/l6fix/clone`, three commits, Java only:
`904392f6` (L6, `IndexDefinition.java`, `IndexDefinitionTester.java`),
`0b32a9f2` (a, `FormatFuzzer.java`), `c760655c` (b,
`KillRestartHarness.java`, `Pack.java`).

**Gates.** On `904392f6`: before-commit OK (88 s), the night tests of
`IndexHarness` OK (158 s, today's seeds, 20768001 among them). On
`c760655c`, the head, one slot at a time, 22:30 to 23:07, all rc = 0
(`l6fix/gates.sh`, summary `l6fix/gates.out`, logs in `l6fix/logs/`):

| Gate                                              | Result, time                  |
|---------------------------------------------------|-------------------------------|
| before-commit                                     | BEFORE COMMIT OK, 87 s        |
| night.sh tests -c IndexHarness (seeds 20768000-7) | SUCCESS, 161 s                |
| the soak's job 6 h2 (seed 20261111001)            | IndexHarness OK, 60 s         |
| FormatFuzzer starts 20768010, 90 s (to 117,650)   | FUZZ OK                       |
| fuzz.sh 2                                         | FUZZ OK, 120 s                |
| kill-restart.sh 1000                              | KILL RESTART OK, 1,425 s      |
| harness-soak.sh -r 2                              | HARNESS SOAK OK, 94 s         |
| level1 full                                       | LEVEL 1 OK, 144 s             |



## State

2026-11-11, 20:19.

* **Ready to land.** Branch `024-24-limits`, head **`b0d41461`**, in
  `/Users/f/fl/bench/2026-11-11/lim3/clone` (main `3dd38b23` merged at
  `c87aa6f9`; main had no code commit after it at 20:18). Every gate of
  section 8 passed on it.
* **Done.** Sections 1 to 8.
* **Open for Frans.** Q1 and Q2 (section 6); QL5's precondition for
  024-17 (section 7, R3); the notes R6, R8 to R11 (section 7).
* **To continue** (if main moves before landing): merge main, rerun
  before-commit, level1, level2 (`lim3/gate.sh`).
* **Landed** as `87afef86`. **The night's fixes** (section 9), 23:08:
  branch `024-24-l6fix`, head **`c760655c`** (three commits on main
  `0f4d1c47`; main had no commit after it at 23:07), in
  `/Users/f/fl/bench/2026-11-11/l6fix/clone`; every gate of section 9
  passed on it. Ready to land.

2026-11-13. Status set after the release (coord-1113).
