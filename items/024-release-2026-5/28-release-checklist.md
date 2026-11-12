# 024-28. The release checklist of 2026.5

Created 2026-11-12 by Frans Lundberg. Status: open.

What stands between `main` on 2026-11-12 (last code commit `5a7f644d`,
09:35, landed as `10408f2b`; items to `ee76b784`, 10:24) and release
2026.5. Frans, 2026-11-12, 10:32: "Are we ready for the release soon?
Now?" Each status names its evidence: a commit, an item and section, a
test or a gate. "Not found" means that this reading found nothing, not
that nothing exists. Read only: nothing built or run. By the agent
"check" of coord-1112, 10:33 to 10:37.


## 1. In short

**Not ready now. Ready after one release night at the earliest, if
Frans takes three decisions.** The code on `main` has no known bug: the
day's changes are each gated (006-22, section 6; 006-23, section 5), and
024-26's apps found none in about 900,000 transactions. What decides it:

1. **No clean night on today's code.** The last `night.sh` (03:05,
   `99722add`) failed one night test, fixed at 06:01 (`6cf6607b`); Java
   changed after it (`0420c72e`, `6cf6607b`, `a7dfb6f7`, `10408f2b`).
   `night.sh large`, s1 on JDK 17 and 27, fuzz on s1, jcstress and
   Android have not run on record format 7 at all (not found). That is
   the release night of section 7, about 8 to 9 hours of the machine.
2. **Aim 4 (the model): proofs or conformance.** The tree model runs
   against Java on every gate (024-12, 024-22), but its main proofs are
   open: TP30 to TP33, the B-tree invariants (TP7), the map (TP10,
   TP11), T4 (section 6). Frans decides whether 2026.5 needs them.
3. **Aims 2 and 3: which open cases may ship as named allowances.**
   The two large cases are fixed (OP1 by 024-07, OP2/ST2 by 024-21);
   the small ones are not touched (OP4, OP8, ST6, ST7, ST8), the
   constants of ST3 and OP3 are not decided (QF1, QF3), and 024-05's
   step 1, the bounds as tests, is not done (section 4).
4. **The notes are almost complete** (`releases/next.md`); two gaps
   (section 7, step 2).


## 2. The aim (024-04)

| Aim | Done                                       | Left                                   |
|---|---|---|
| 1 bugs   | no known bug; 024-26 found none      | a clean release night (section 7)      |
| 2 ops    | OP1 fixed (024-07), OP2 (024-21)     | OP4, OP8 small; OP3's constant (QF3)   |
| 3 storage | ST2 (024-21), ST4 (024-23), ST1 (024-15) | ST6, ST7, ST8 small; ST3 (QF1)   |
| 4 model  | tie (024-09), tree in Lean (024-12, 024-22) | the proofs (section 6), a decision |

* **Aim 1.** 024-26: no bug, Javadoc findings U26-1 to U26-8, made by
  024-27 (`a7dfb6f7`). The last bugs found were by the night runs of
  2026-11-11: four from the limits (fixed by 23:07, `1f01c5f6`) and a
  stale constant after CRC32C (`6cf6607b`) (006-22, section 6).
* **Aim 2.** The two cases 024-05 found by a wide margin are fixed:
  the last touch (024-07, `a780b957`: the last step's record 29 kB at
  10M keys, not 206 MB) and the work after sparse deletes (024-21,
  `67925924`). Left: the small cases and the constants (section 3).
* **Aim 3.** Merges keep every key node at m = 8 or more (BU1, 024-21);
  dead klongs at most theta a node (024-23, `08659847`); the cost of key
  shape is within the aim, documented and bounded (024-04, section 7,
  log 07:30; 024-15, `1e77cfc6`). Left: the small cases, ST3's constant.
* **Aim 4.** "The model matches" as 024-04, section 6, reads it: the tie
  repaired (024-09, `379d8acf`), the tree in Lean run against Java
  (024-12, `b84cf761`; merges 024-22), new changes model first (024-22,
  024-23). "The proofs begun on the stable parts and finished as the
  algorithms settle": begun, not finished (section 6).


## 3. The known cases (024-05, sections 2 and 3)

"Breaks": 024-05's column (does the case break the aim: yes, might,
no). Status today with its evidence.

| ID   | Breaks | Status today                                  | Evidence                        |
|---|---|---|---|
| OP1  | yes    | fixed                                         | 024-07; `a780b957`              |
| OP2  | yes    | fixed: merges, record format 7                | 024-21, 024-22; `67925924`      |
| OP3  | might  | open: by design, constant undecided           | 024-05, QF3; no answer found    |
| OP4  | yes    | open: the pace's cap not made                 | 015-84 open (015's readme)      |
| OP5  | might  | named allowance (Frans, 2026-10-28)           | 024-05, OP5; 010-01, P4         |
| OP6  | yes    | out by the limit: a key at most 111 bytes     | 024-24, L2; `7c255127`          |
| OP7  | might  | open: T4 not proved; cold start 46 s on s1    | 024-05, OP7; 005-57             |
| OP8  | might  | open: not touched                             | 024-07, section 10 ("OP8, ST7") |
| OP9  | no     | within the aim; P8 not started                | 024-03, CL1                     |
| OP10 | might  | open: not attributed; no ZGC run (GM6)        | 024-05, OP10; not found         |
| OP11 | no     | none needed                                   | 023-09, 5.3                     |
| ST1  | might  | within aim 3 (Frans), documented, bounded     | 024-04, 7; 024-15; `1e77cfc6`   |
| ST2  | yes    | fixed: BU1, 1.29 to 1.90 x the twin at 1M     | 024-21, sections 1, 8.1         |
| ST3  | might  | open: by design, constant undecided           | 024-05, QF1; no answer found    |
| ST4  | yes    | fixed: option 2, theta 7 at node size 30      | 024-23; `08659847`              |
| ST5  | no     | named allowance; fix (a) dropped              | 023-10; 024's readme, Log       |
| ST6  | yes    | open: no change found                         | no commit found                 |
| ST7  | yes    | open: `KeyAccessPath.clear` keeps the arrays  | `bergdb.dag.KeyAccessPath`      |
| ST8  | yes    | open: the 10 MB write buffer                  | `StorageManager`, 10 * 1000000  |
| ST9  | no     | by design                                     | levels.md, 7                    |
| ST10 | no     | by design                                     | levels.md, 7                    |
| ST11 | no     | a non-goal                                    | levels.md, 6                    |

The small ones:

* **OP4, the pace's cap.** 015-84 is an "investigate" entry, open,
  "registered only; nothing run or changed". 024-05 (step 2) put it
  with OP1's batch; 024-07 did not take it.
* **OP6, long keys.** The case was 2.6 to 48 s for keys of 1 to 4 MB.
  L2 (111 bytes, 16 segments) makes such a key impossible: refused with
  `IllegalArgumentException` (024-24; next.md, "Limits"). Closed by the
  limit, not by 021-16's fix.
* **OP8, a step's value reads.** 024-07, section 10: "OP8, ST7 ... not
  touched". No commit found.
* **ST6, the cache's tables.** No commit or item found since 024-05.
  Also on 024's planned list (section 5).
* **ST7, the path arrays.** `KeyAccessPath.clear()` nulls the used
  entries and keeps the arrays, as 024-05 read it. 024-07 removed the
  cause (no key range), so the arrays now follow the longest path, not
  a range; the shrink itself is not made.
* **ST8, an empty database's heap.** `StorageManager.DEFAULT_BUFFER_SIZE`
  is still `10 * 1000000`.


## 4. The bounds (024-05, section 4)

None of BD1 to BD14 is decided as a bound (024-05: "none is decided");
QF1 to QF8 have no answer found, but some were answered in effect by
later decisions (noted).

| BD   | Checked today by                                   | Waits for     |
|---|---|---|
| BD1  | record: only the limit (`testLastStepWithinRecordLimit`) | QF6      |
| BD2  | nothing at 1M keys or more                          | QF6, GM6      |
| BD3  | nothing                                             | -             |
| BD4  | the count: `MergeTester.testSparseAgainstTwin` (BU2) | -            |
| BD5  | `level1.sh` SS limits at small size                 | QF3           |
| BD6  | `T3_take` (proved); `performance.sh` restarts       | -             |
| BD7  | `Reclaim.Tester.testStepDirtiesItsPathsOnly` (<= 63) | -            |
| BD8  | nothing                                             | -             |
| BD9  | nothing                                             | -             |
| BD10 | nothing; `performance.sh` reports `kept_mb_max`     | QF1           |
| BD11 | LargerThanMemory (`level4.sh`, step 6), pass/fail   | QF4           |
| BD12 | `level1.sh`: MEM <= 131, SEG <= 230, MEM10M <= 131  | QF4 (in effect) |
| BD13 | `testSparseAgainstTwin` (3,000 keys); 024-21's 8.1  | QF2 (in effect) |
| BD14 | nothing                                             | -             |

* **BD4, BD13.** `MergeTester.testSparseAgainstTwin` asserts BU2 (at
  most 2 times the twin's key nodes) at 3,000 keys, in the unit tests
  (024-21, TU3); at 100,000 and 1M keys by hand (024-21, section 8.1);
  at 10M once, 1.43 times (024-21, TU10, "part"). The scan's own count
  (023-03's T3) was not run (024-21, section 5.2).
* **BD12.** MEM10M is checked in a full `level1.sh` only (024-15).
* **BD7.** 024-07's B1; and the record limit's test (024-07, section 3).
* **QF answered in effect:** QF2 (strict) by the merges and BU1 (024-11,
  024-21, Frans 2026-11-11); QF5 (key shape documented) by 024-04's log
  of 07:30 and 024-15; QF4 in part by 024-15's MEM10M and SEG. **Open:**
  QF1, QF3, QF6, QF7, QF8.

**024-05's order of work, step 1** ("023-03's tests as code, with PF1's
record counter as a night step"): **not done.** 023-03's T1 to T4 still
live in the prototype `CleanupRule`, not on `main` (024-21, section
5.2); `night.sh`'s steps have no record counter and no run above 1M
keys but MEM10M (`java/night.sh`, the `step` lines). GM1 done (024-08);
GM2 done in part (024-07: the cause; "keys put ahead of the scan, at
scale" not run, its section 10); GM3 replaced by 024-14's shapes at 1M
and 10M on a measuring build; GM4 to GM8 not found. **A run of 024-03's
set (PF1) on format 7 at 10M keys: not found** (024-23, next.md: "Not
yet measured: 10M keys, memory, reads"; 024-19 has counts at 10M).


## 5. The planned list (024's readme, "Planned so far")

| Entry                                   | Status                                  |
|---|---|
| The builder's rule "the last operation wins" | done, made strict: 024-10, 024-16 |
| P8, each reclaim step at its own time   | not started; "not needed" (024-03, CL1) |
| Merges at the delete                    | done: 024-21, 024-22 (`67925924`)       |
| Fix (a) of the dirty top-node window    | dropped: 023-10 (024's Log, 2026-11-10) |
| `maintain()`                            | not started; no item found              |
| The cache's tables (ST6)                | not started; no item found              |
| The last touch of a reclaim iteration   | done: 024-07 (`a780b957`)               |
| Dead klongs in live nodes               | done: 024-23, option 2 (`08659847`)     |
| A time klong's unused bits              | done: `0420c72e` (024-25, section 12)   |

* **P8.** No decision of Frans found that takes it out; 024-05 (step 2)
  keeps it out "unless GM2 shows keys put ahead of the scan at random to
  be a case", and that half of GM2 was not run.
* **`maintain()`** (023-04, Y10): named only in 024-01, 024-05 and
  024-06; it would change reclaim's step (024-05, section 6).


## 6. Aim 4, the model

**Proved** (`#print axioms` standard, each in its item):

* The tie: `PhysStep` (024-09, A2); T-COVER and T-LATEST, the last
  touch's cut (024-07, section 4); `T3_take` (007).
* The tree: TP13 `SpecOKTree`, TP17, TP18, and the model's run has the
  tree's P (024-12, section 6); TP28, TP34 to TP38, the merge's local
  parts (024-22, section 6); `ReleaseFits`, the limits' nodes fit a
  record (024-24, section 1); the writer's frame and TP32 under a height
  premise (`08559fff`, `2c37bfeb`).

**Checked by conformance only** (run, not proved): Java equals the model
on every trace of `treeconf.sh` (`level2.sh` step 8; 115 traces, 024-12),
with merges on 260 traces (024-22) and option 2 on 222 (024-23);
`treetest` exhaustive at small node sizes; `tree-tests` in `night.sh`.
T-SCHEME by argument and 90 reclaim traces (024-09). The other 24 of
024-12's 27 properties hold on every traced state (TP7 the invariants,
TP10 get, TP11 scan, TP21 and TP22 the storage bounds, TP23 and TP26
the dirty-node bounds).

**Open:**

* **024-22: TP30** (V1 kept, the large part of the B-tree proof),
  **TP31** (BU1's count), **TP32** (merges a transaction, restated with
  sorted premises, `c0a8cadf`, not proved), **TP33** (CB3, potential).
* **T4** (the records at the section's ends; 024-05, OP7): not proved.
* **024-12's open items** (section 9): the proofs in its order (TP9,
  TP1, then TP7 with TP8 and TP4, then TP27); `treeconf.sh large`;
  traces with keys of raw bytes (`shape=bytes`). 024-22's too: `set6.sh`
  at 8/17/17 and `treeconf.sh large` with merges (section 11).
* **024-06's questions 3 to 8:** no answers found as such. In effect: 3
  (compaction never in place) followed by 024-23 (a new node); 4 (keys in
  the trace) done by 024-12 (trace format 3); 6 (the gates) done by
  024-09 and 024-12 (`level2.sh`, `unlinkfuzz.sh`); 7 (A6) by 024-09's
  follow-up (`751bb653`, A6 required) and 024-22, QM4. Open: 5 (which
  cost statements go to Lean) and 8 (025-01 against the proofs).

**Frans's decision (blocking):** does 2026.5 require the proofs of the
tree (TP30 to TP33, TP7, TP10 and TP11, T4), or does it ship with
conformance plus the proofs that hold? 024-06's question 1 recommended
(b), the tree in Lean run against Java, for 2026.5 and (c), its proofs,
started once the algorithms are in; 024-04, section 6 says "the proofs
begun on the stable parts and finished as the algorithms settle". By
024-06's guess, C1 and C2 are each "one to two weeks of agent work ...
with an uncertain end" (024-06, section 5.1).


## 7. The release process

As 2026.4's (020-31; 006-21, section 8), for 2026.5:

1. **Frans's decisions** of section 8's blocking list.
2. **`releases/next.md` complete.** Has: format 7, merges, theta, CRC32C,
   the last touch, the builder's rule, one operation a key, the limits,
   a refused call spoils the builder. Missing: the time klong's check
   (`0420c72e`, not found in next.md); 024-07's StreamDigest names ("not
   yet named", next.md; 024-25, section 7 has all 48 digests changed);
   62 as the largest node size (024-27, section 5; not found in next.md).
3. **docs/ current.** `docs/levels.md` updated through 024-27
   (`ac0e4bdf`); `docs/sis-model.md` for the merges (`0385609a`); a
   reading of both for the release: not done.
4. **Commit A in a release clone**: `main`, BuildInfo `2026.5` (now
   `2026.5-dev`) with its build number, the notes; `before-commit.sh`
   in a fresh clone. The main tree has an uncommitted change of
   `java/src/bergdb/pubimp/RwEnvironmentImp.java` (git status, 10:33):
   another session's; it must not enter A unless landed.
5. **The night**, as 020-31, section 2: F53 `night.sh large` on A (about
   6.5 h; conformance-large 16,112 s in 2026.4), then jcstress (8
   tests), checks (StreamDigest against 2026.4: all configurations
   differ by format 7, each named in next.md; the Lean axioms), Android
   (`java/stress/android.sh`, asked by Frans, 006-18-03); the regular
   `night.sh` (about 100 min); s1: unit, F and night tests on JDK 27 and
   17 and the user's program, then UnlinkFuzz in 8 configurations
   (2026.4: 34,650 and 5,950 seeds, 0 failures). The scripts of
   `/Users/f/fl/bench/2026-11-10/rel/` to adapt (`conductor.sh`,
   `morning/`).
6. **The morning**: `clean.sh` (NIGHT CLEAN), `to-main.sh`,
   `release.sh`: the jar, zips, `baseline.zip`, `SHA256SUMS`, the notes
   in `releases/2026.5/`, next.md emptied, README.md, BuildInfo
   2026.6-dev, docs/log.md's entry, commit B, the tag `release-2026.5`
   on A, push with the tag.
7. **The C clone**: matches release 2026.4 (022-07, `51a7224c`), not
   format 7. In 2026.4 it was not a release step (it followed, 022-07).
   Whether 022 follows 2026.5 is Frans's (022's readme: "I will decide
   later how long to update it").

Fuzz seeds: 2026.4 ran UnlinkFuzz from 1,000,001 on A and 2,000,001 on
A' (020-31, section 1.2); CorruptStreamTester takes the day's seed, so
a failure there may be an old damaged-stream weakness (020-31, 6), now
low priority (Frans, 2026-11-12, 07:26: "best effort").


## 8. Open questions for Frans

**Block the release:**

* **024-06, Q1 / 024-04, 6**: the proofs required, or conformance plus
  the proofs that hold (section 6).
* **024-05, QF1**: ST3's constant (4.5 to 6 times a fresh stream).
* **024-05, QF3**: OP3, a put's bytes growing with log K at fixed sd.
* **024-05, QF6 and step 1**: bounds as gates (counts) before the
  release, or after.
* **024-05, QF8 / 015-84**: OP4's cap in 2026.5, or later.
* **The small cases OP8, ST6, ST7, ST8, `maintain()`, P8**: in 2026.5,
  or named and moved (026 or later). No decision found for any.
* **Changed tests to see** (006-22, section 6, point 6; no answer
  found): 024-21 QJ1, 024-23 section 4.1, 024-24 Q2, 024-25 QC2;
  accepted by the coordinator under the delegation of 2026-11-11, 14:48
  and 17:43. Blocks only if the delegation does not cover the release.

**Do not block:**

* 024-05, QF7 (100M keys or 10M with a scale law).
* 024-06, Q5 and Q8 (cost statements in Lean; 025-01).
* 024-02, Q14 and Q16 (reserved bytes zero; unknown node types),
  "maybe" in 2026.5 (024-04, section 5); damaged streams low priority.
* 024-08, Q2 and Q3 (Mem's keys; 024-03's 327 corrected).
* 024-19, Q2 and Q3 (B a property of the database; thresholds v*B/30);
  Q5 proposed for 2026.6 (026's readme).
* 024-21, QJ2 (thrash at node size 8).
* 024-23, QO1 and QO3 (defaults).
* 024-24, Q1 (no index entry for levels over 111 bytes).
* 024-25, QC3 (017-08's other checksums).
* 024-18, QD2 to QD5 (after option 2).
* 024-10, QL1 to QL5 (superseded by 024-16; not marked decided).
* 022: whether the C clone follows 2026.5.
* 023-03, Q3: R9's constants c = c' = 2.


## 9. State

2026-11-12, 10:37, by the agent "check" of coord-1112. Read only at
`main` `ee76b784`; nothing built, run or committed.

* **Done.** Sections 1 to 8, from 024's readme, 024-04, 024-05, 024-06
  (5, 7), 024-07 (10), 024-12 (1, 6, 9), 024-21 (5, 9), 024-22 (6, 9 to
  11), 024-24 (1, 6), the question sections of 024-08, 10, 11, 18, 19,
  23, 25, 27; 006-21 (8, 9), 006-22 (6), 006-23; 020-31; 022's readme;
  026's readme; `releases/next.md`; `git log` since 2026-11-11;
  `java/night.sh`, `level1.sh`, `level4.sh`; the night reports in
  `java/build/night/`; in the code `KeyAccessPath.clear`,
  `StorageManager.DEFAULT_BUFFER_SIZE`, BuildInfo, the named tests.
* **Not read:** 024-01, 024-02, 024-03 in full; 024-13 to 024-20 but
  their readme lines; 015-84 beyond its head; `docs/levels.md` and
  `docs/sis-model.md` for completeness. Not checked: whether
  `e7488080` made 024-12's TP15 a proved line.
* **To continue:** after Frans's answers to section 8's blocking list,
  turn section 7 into the night's plan (020-31's scripts).
