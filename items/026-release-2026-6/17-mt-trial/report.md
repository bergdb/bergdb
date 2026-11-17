# 026-17, MT's trial: the report

The counts in full behind 026-17's "Result" section. Written 2026-11-16 by
agent A of coord-1116 in step T8, from the runs of T4 to T6 (agent B's
program, `MtTest.lean`), T3's review and T7's counts. Times are from `date`.
The code is on the branch `026-17-mt-trial` in the trial's clone, kept in the
main repository, not merged. The files of this directory are listed in
section 10.

# 1. What ran

- **The clone:** `/Users/f/fl/bench/026-17/bergdb` at main 00a3a29b. The
  branch adds `lean/SIS/Tree/Mt.lean`, `lean/MtTest.lean`, `lean/MtDeps.lean`
  and the stanza `mttest` in `lean/lakefile.toml`. Nothing else changed.
- **The steps:**
  - T0 done 11:18 (`treetest` built in 10 s);
  - T1 (Mt.lean) 11:19 to 11:35;
  - T2 (the program) done 11:42;
  - T3 (the review) done 11:50;
  - T2's fixes after the review 12:00;
  - T4 (the first runs) done 12:06;
  - T7 (the complexity) done 12:12;
  - T5 (node size 30) done 12:25;
  - T6 (node size 8) done 12:34;
  - T8 done 13:36.
- **Usage:** the week was at 93 % at T0 (11:17) and at 94 % at 13:30.
- **The commits that the runs used:** Mt.lean 50c728ed (A1 included);
  MtTest.lean 3fc53c79, which reads by A1 at untidy boundaries. T4 ran the
  binary of bbe873fc on Mt.lean 5223d5e1, before A1.
- **The parameters:**
  - node size 30: `({M := 30, G := 2, H := 6}).withMerges.withTheta`,
    that is m = 8, h = c = 17, theta = 7;
  - node size 8: G = 2, H = 8, so m = 2, h = c = 4, theta = 2.

# 2. The checks, run by run

Every run below ended with `MTTEST OK`, and none was killed. Every one had
0 failures of K1 to K7, A6 and Skip, 0 `bounds:` errors, 0 faults of K4 at
tidy boundaries, and 0 second-pass fix steps (K7).

Column key for the two tables:

- **bnd**: boundaries;
- **dels**: deleted keys;
- **fix/del**: fix steps for each deleted key;
- **most**: the most fix steps of one group;
- **made**, **B-new**, **B-all**, **idx B-new**: MT against today. The
  last is B-new for the index alone.

Node size 30, T5 (`runs/30-*.txt`):

| run | groups | bnd | untidy | dels | fix/del | most | made | B-new | B-all | idx B-new |
|---|---|---|---|---|---|---|---|---|---|---|
| 30-A | 2766 | 2845 | 79 | 2551 | 0.031 | 2 | 1.01 | 1.01 | 1.02 | 1.01 |
| 30-B | 1965 | 2376 | 411 | 8732 | 0.047 | 4 | 1.01 | 1.02 | 1.03 | 1.03 |
| 30-C | 2100 | 2405 | 305 | 6348 | 0.048 | 3 | 1.01 | 1.01 | 1.02 | 1.02 |
| 30-D | 4470 | 5335 | 865 | 8000 | 0.108 | 10 | 1.12 | 1.08 | 1.12 | 1.11 |
| 30-E | 3072 | 3626 | 554 | 6000 | 0.092 | 110 | 1.71 | 1.15 | 1.17 | 1.24 |
| 30-F | 3540 | 4180 | 640 | 6000 | 0.107 | 7 | 1.03 | 1.05 | 1.09 | 1.07 |
| 30-G | 8736 | 9371 | 635 | 7800 | 0.081 | 10 | 1.02 | 1.03 | 1.05 | 1.05 |
| 30-H | 660 | 1879 | 1219 | 12000 | 0.102 | 8 | 1.07 | 1.08 | 1.12 | 1.11 |

Totals at node size 30: 27,309 groups; 32,017 boundaries, 4,708 of them
untidy; 4,708 fix steps for 57,431 deleted keys, which is 0.082 a deleted
key.

Node size 8, T6 (`runs/8-*.txt`). Q1 to Q4 and Q6 only; section 6.2 of the
plan does not read its costs.

| run | groups | bnd | untidy | dels | fix/del | most | made | B-new | B-all | idx B-new |
|---|---|---|---|---|---|---|---|---|---|---|
| 8-D | 894 | 1783 | 889 | 1600 | 0.556 | 57 | 1.33 | 1.36 | 1.48 | 1.44 |
| 8-exh-2-12-2-pairs | 82902 | 116092 | 33190 | 73416 | 0.452 | 5 | 1.06 | 1.18 | 1.24 | 1.21 |
| 8-exh-3-12-2 | 13596 | 16529 | 2933 | 6516 | 0.450 | 2 | 1.00 | 1.13 | 1.16 | 1.15 |
| 8-exh-3-12-4 | 13608 | 21722 | 8114 | 6516 | 1.245 | 4 | 1.44 | 1.47 | 1.49 | 1.53 |
| 8-random-10-200-124 | 1847 | 2675 | 828 | 1619 | 0.511 | 6 | 1.18 | 1.20 | 1.24 | 1.26 |
| 8-random-20-200-40 | 3657 | 4999 | 1342 | 3107 | 0.432 | 5 | 1.16 | 1.17 | 1.20 | 1.21 |
| 8-subsets-12-2-0 | 4107 | 15890 | 11783 | 24576 | 0.479 | 8 | 2.12 | 1.96 | 2.32 | 1.96 |
| 8-subsets-210-0-1-puts | 16373 | 16391 | 18 | 5120 | 0.004 | 1 | 1.00 | 1.00 | 1.00 | 1.00 |
| 8-subsets-9-3-0-puts | 19692 | 102154 | 82462 | 59049 | 1.397 | 8 | 3.01 | 2.60 | 3.00 | 2.99 |

Totals at node size 8: 156,676 groups; 298,235 boundaries, 141,559 of them
untidy.

**T4** (`runs/t4-*.txt`), on the binary before A1:

- MT on family A (10 seeds x 300): 2,845 boundaries, 79 untidy, green.
- MT on `subsets 8 12 2 0`: 15,890 boundaries, 11,783 untidy, green.
- The mutant, whose driver stops one fix step early: K4 found faults at
  297 tidy boundaries (A, 3 seeds) and at 4,019 (subsets). So the checks
  bite.

**T2's selftest** (`runs/t2*-selftest-*.txt`, `runs/t5-selftest-A.txt`)
runs today's writer in MT's place. It was green on A to H and on
`subsets 8 12 2 0`. `selfmutant` (merges off, checks on) made K4 find
faults.

# 3. Q1 to Q4: what passed, and on what

- **Q1, nothing taken back.**
  - The evidence: K3 at every transaction of every run. Every key node in
    a transaction's `changesOf.new` is reachable at its time, `W.taken` is
    empty, and a top node it made is the super root.
  - The two `MT:` errors of Mt.lean cannot fire. A fix step finds its
    target before it writes (T3, finding 3), so they are guards, not
    evidence.
  - Entries, not nodes, are still taken back by `toPrev` in the user
    transaction's split (section 7).
- **Q2, every get and scan at every boundary.**
  - K1 at every boundary and K2 at each run's end: green, with A1 at
    untidy boundaries.
  - Without A1, scans failed after mass deletes (section 5): 325 untidy
    scans at 56 boundaries of 30-E, and 17,448 at 21 boundaries of 8-D.
    Gets never failed.
- **Q3, after the last fix step, today's invariants.**
  - K4 (`faultsAt`, the pointers, BU1, `balanced`) at every tidy boundary:
    0 faults.
  - K5 at every untidy boundary: only `NonEmptyOK`, `RootsOK` and
    `FillOK`, and only at nodes on the path of a pending key (the strict
    set: the current key and the keys after it).
  - The tree against today's, by shape, at node size 30 (5.4):
    - equal in 9,690 groups without deletes, 12,427 with one delete and
      5,031 with several;
    - different in 0, 6 and 155 groups of those kinds: 161 of 27,309.
  - Why they differ: MT merges after all of a transaction's operations,
    and today's writer merges inside each delete, before the operations
    after it. So a merge meets other fills. MT's tree has a few key nodes
    more in A to C (+6, +15, +4 over the family's different groups) and
    fewer in D to H (−10, −2, −9, −5, −11). The height differed in 1
    group, in E, where MT's tree was lower.
- **Q4, the fixing ends.**
  - No group reached the driver's fuel. The nearest were 74 of 416,000 in
    30-E and 5 of 320 in 8-D.
  - K6 (a fix step that is not needed changes nothing) and K7 (one pass
    is enough) were green in every run.
  - The fuel is a guard, not a proved bound. Section 3.4's argument holds
    for no single key (T3, finding 1), so the fuel is the group's
    (`Mt.groupFuel`).

# 4. Q5 and 5.6: the counts

All of these are at node size 30.

- **Fix steps:**
  - 0.082 a deleted key over all. By family: A 0.031, B 0.047, C 0.048,
    D 0.108, E 0.092, F 0.107, G 0.081, H 0.102.
  - A group's most is 10, except E's mass deletes: 38 to 110 steps for
    one transaction of 500 or 1,000 deletes, still about 0.1 a deleted
    key.
  - Groups of one delete (counts for a key, T3, finding 2), by the height
    of the key's segment tree:
    - D: height 0 0.03, 1 0.13, 2 0.11, most 3;
    - F: 0.03, 0.14 and 0.09, most 3;
    - G: height 0 0.06, height 1 0.10;
    - B and C: 0.02 to 0.03.
  - H (height 3, 20 deletes a group): 0.10 a deleted key as its group's
    mean, most 0.40.
- **Fix steps by kind** (all runs at 30):
  - fix.merge.one 3,324 and fix.merge.two 999 (of them fix.merge.inner
    275, fix.merge.empty 423, fix.merge.bothempty 117);
  - fix.unlink 287;
  - fix.collapse.space 48, fix.collapse.segment 50;
  - fix.pass.onlychild 46.
- **Inside fix steps:**
  - merge.parent.full 113, merge.parent.dead 803;
  - split.time1 793, split.time2 230, split.space1 12, split.space2 5,
    split.space3 0;
  - bitmap.full 7, bitmap.dead 26.
- **Bytes**, by 5.5's layout and stand-ins (48 bytes a record and 16 a
  changed node, 8 bytes a value, 32 + 8 k a fix node):

  | measure | MT | today | ratio |
  |---|---|---|---|
  | B-new | 16,319,452 | 15,564,724 | 1.048 |
  | B-all | 49,738,188 | 46,956,036 | 1.059 |
  | B-new, the index alone | 11,135,428 | 10,380,700 | 1.073 |
  | B-all, the index alone | 44,554,164 | 41,772,012 | 1.067 |

  - Nodes made: 22,295 against 20,641 (1.080); changed 1.073; klongs
    1.040.
  - A deleted key: 13.1 bytes more B-new, 48.4 more B-all, 0.029 nodes
    more made.
  - Family C, the mixed one (the user's number): B-new 1.01, B-all 1.02.
- **Today's take-backs:** 1,803 for 4,753 merges, 0.38 a merge, set
  beside 024-22, section 2.9. MT has none.
- **The height between:**
  - MT's greatest height over a group was never above both the height
    before and today's after (0 groups).
  - H needed: 3 for both, in H; 1 or 2 elsewhere.
  - At node size 8 it was one above in 18,603 groups, always by 1. H
    needed was the same for both, but in `subsets 8 12 2 0` (MT 2,
    today 1).
- **The untidy states:**
  - 4,708 boundaries.
  - The most key nodes with a fill fault at one boundary: 99 (E); 2 to 8
    elsewhere.
  - Boundaries with an index node that has no live key below it
    (reclaim's premise, 006-28, 7.4): 759 (E 393, G 278, D 78, F 6,
    H 4), at most 110 such nodes at one boundary (E).
- **Top nodes made:** by fix steps 278 and by MT's user transactions 295,
  against today's 528 (1.09).

# 5. The scan finding and rule A1

- **What failed:** only scans (Read.lean's `scan`) at untidy boundaries
  after mass deletes, and the same times read later (K2). Every get was
  right. First seen in agent B's smoke run of E (`runs/t2fix-smoke-mt-E.txt`:
  K1 325, K2 5).
- **The smallest run,** at node size 30 with 6.1's parameters:
  - put the keys [64 j + 8], j = 0 to 376, in one user transaction;
  - delete j = 1 to 375 in one;
  - at the boundary right after the delete (untidy, before any fix
    step) 25 empty leaves lie side by side;
  - `scan` forward from the start gives key 0 only, backward key 376
    only;
  - with 374 deleted (24 empty leaves), both are right.

  Smaller still, at node size 8 with G = 0 and H = 3: 21 keys put, 19
  deleted (Mt.lean's guard 11). The script is `scripts/scan-smallest.lean.txt`.
- **The cause:**
  - `scanGo` gives each `next` (`nextGo`) a fuel of 2 · p.fuel + 2 steps,
    54 at node size 30. Its comment sizes that budget by TP27's premise,
    a live key below every index node (TP7, TP11).
  - Each empty leaf costs a `next` two steps, down and up. After about 25
    in a row the fuel ends, and the scan ends as at the database's end.
  - With more fuel the same steps give every KV: on the smallest run and
    on E's 1,000 keys with half deleted, which has 35 empty leaves.
- **Java's reader:** `GetMany.Chain.next()` (java/src/bergdb/dag/GetMany.java,
  lines 385 to 470) is a `while (true)` loop with no bound. `setup()`
  (283 to 345) goes down one path and handles a node with no klong. By
  reading (not run), Java's scan is right over empty leaves and empty
  segment trees. What changes is its cost at an untidy time: two node
  visits for each empty key node crossed. Those times stay readable
  until reclaim cuts them.
- **By the plan's 2.3:**
  - It is not a slip in Mt.lean: R1 leaves empty leaves by design.
  - It is not a slip in MtTest: K1 compares the model's scan with a right
    reference.
  - The two readings of S2:
    - **A1:** BergDB's reader needs no change, and the model's budget is
      an artifact. `Mt.scanWith` is the scan with a given fuel, and
      `Mt.scanFuel p n = 2 p.fuel + 2 + 2 n` suffices for a tree of at
      most n key nodes. This is agent A's choice, which the coordinator
      accepted provisionally (Mt.lean 50c728ed; MtTest 3fc53c79 reads by
      it at untidy boundaries, and by today's `scan` at tidy ones).
    - **Strict:** a reader that must change for MT, so S2: MT is off as
      specified.
  - Frans decides.
- **Under 026-18** (main transactions of subtransactions; readers see
  only the states between main transactions) neither reading applies.
  No reader meets an untidy state; scans keep TP27 and today's budget.
- **What it means for the proofs if readers do see untidy states:** the
  scan's proofs (TP7, TP11) rest on nonempty children. For MT they would
  need a measure that counts empty subtrees.

# 6. Q6: the two new rules

- **R3, the merge of an empty leaf, passes.**
  - At node size 30: 423 times, 117 of them of two empty leaves. At node
    size 8: 9,554, 111 of two empty leaves.
  - Q1 to Q4 passed on the runs that reach it.
  - An empty leaf merged into two nodes (T3, finding 6) was not reached
    at either size.
- **R4, the only child passed over, is "not reached" at node size 30.**
  - 46 times at 30 (E 42, D 2, H 2), under Q6's 100.
  - At node size 8: 1,248 times in T6's treetest sets, 1,318 with D.
  - Also in guards 4 and 5.
- **The rest of Q6 held:**
  - `LeftmostOK` held at every boundary, with no exception in K5, so LE-b
    is not needed.
  - No inner node was ever empty: no `MT: an empty inner node`.
  - No rule beyond section 3 was needed in the writer. A1 is a rule of
    the model's reader.

# 7. Q7: the complexity (T7)

From `lake env lean MtDeps.lean` (`scripts/deps.txt`) and
`scripts/counts.py` (`scripts/counts.txt`). The walk takes today's writer
from `exec?`, and MT's from `runUser`, `runFix` and `fixAll` with
`changesOf`. Matchers and proofs are followed but never counted as a use.

- **C1, added.** Mt.lean is 637 lines, 372 of them code.
  - MT's writer, R1 to R5, is 373 lines (252 code). Of these, 115 are
    copied with changes from Exec.lean (`setValue`, `putSegs`, `putKv`,
    `runWith` from `runOpsFrom`, and `merge`), and 258 are new.
  - By part:
    - R1's wrappers 82;
    - the path and the target 74;
    - the merge 69;
    - the other fixes and the step 57;
    - the driver 91.
  - Besides the writer:
    - A1 30;
    - `pathAt` 15;
    - the 11 guards 155;
    - the header and comments 64.
- **C2, freed:** 16 definitions, 329 lines (244 code).
  - The list: `afterDelete`, `boundsOK`, `canTakeBack`, `climb`,
    `collapseRoot`, `deleteUpward`, `descendHeight`, `descendToHeight`,
    `descendToSegmentRoot`, `emptyKeyNext`, `mergeUp`, `retarget`,
    `takeBack`, `takeBackRoot`, `takenBack` (Exec.lean) and
    `KNode.smallestLive` (Node.lean).
  - A grep of Mt.lean's code finds none of them.
  - Replaced by MT's copies: `exec?`, `runOps`, `runOpsFrom`, `setValue`,
    `putSegs`, `putKv` and `merge` (141 lines).
- **Kept by the split's code.** Each of these stays in MT, and each does
  something or nothing:
  - `toPrev` (`handleFullWith`, `unlink`): kept and live. In a user
    transaction a node changed by an earlier operation and split by a
    later one loses its entries of that time. It is a no-op in a fix
    step.
  - `unlink` (`replaceRoot`): kept, dead. A collapsed root has no klong of
    the step's time.
  - `replacedBy`, `setMadeFor` and `W.madeFor` (`handleFullWith`): kept,
    dead. `madeFor` is written and read only to be written again.
  - `W.taken` (`changesOf`): kept, dead. MT never writes it, so it is
    always empty.
  - `W.outside`: kept and live. MT's `boundsNow` decides by it (D3).
  - Freeing the dead ones needs edits of `handleFullWith`, `replaceRoot`
    and `changesOf` that the trial does not make.
- **C3, net.**
  - Exec.lean has 1,175 lines (829 code). Take away the freed definitions
    and the originals of the copies, 459 lines (345 code), and add MT's
    writer, 373 (252).
  - The result is 1,089 lines (736 code): 86 fewer (93 fewer of code).
  - Besides, 11 lines are freed in Node.lean.
- **C4, the proofs that name what is freed.** This uses 006-28's method
  over lean/SIS/Tree without Mt.lean (474 files, 167,243 lines):
  - the 16 freed names:
    - by name: 459 declarations, 14,131 lines, 8.4 %;
    - by text: 833 declarations, 33,277 lines, 19.9 % (18.6 % without
      comments);
  - the kept-dead names (`replacedBy`, `setMadeFor`, `madeFor`,
    `W.taken`, `unlink`):
    - by name: 1,594 lines;
    - by text: 45.8 %;
  - both: 9.4 % by name, 53.2 % by text;
  - for context, the copied originals: 29.0 % by text, 17.0 % without
    comments.

  How rough this is:
  - A declaration counts whole if it names one of these once.
  - Names match as substrings.
  - Nothing is built.
  - "By text" bounds from above what a change to these definitions
    touches, not what MT would free. "By name" is nearer to the proofs
    about them.
- **C5, the invariant between:** MtTest's `k5Allowed`, 5 lines of code,
  with `Mt.pathAt` (15 lines) for the pending keys' paths.
- **C1 against C2 (the plan asks for this first):** C1 is above C2. The
  writer's 373 lines are above the 329 freed; only with the copied
  originals (459) is the net smaller.

# 8. Where Mt.lean leaves section 3, and the review

- **The deviations** (Mt.lean's header):
  - **D1:** it imports `SIS.Tree.Inv`, for the guards.
  - **D2:** the check for an empty inner node runs at every depth.
  - **D3:** the bounds are checked after each operation and fix step.
  - **D4:** `key` is dropped from `setValue` and `putSegs`.
  - **D5:** helpers for the program (`deletedKeys`, `Step`, `cut`,
    `pathAt`, `runWith`).
  - **D6:** `runFix` needs the merges on.
  - **D7:** extra notes.
  - **D8:** the fuel is the group's.
  - **D9:** two `Bug:` checks that cannot fail.
- **The rule added:** A1 (section 5).
- **T3's review** (`t3-review.md`): 0 must fix, 3 should fix, 8 notes.
  - Finding 1, the fuel: mended (5e8d25ec).
  - Findings 2 and 9, counts a key and K5's pending keys: mended in
    MtTest (bbe873fc).
  - Finding 7, the cascades of a fix step: added to guards 2 and 5
    (5223d5e1).
  - The rest: notes, answered in `state.md`.

# 9. Not reached, cut, not done

- **Cut:** nothing. Families A to H ran as section 6.1 has them, and node
  size 8 ran as 6.2.
- **Not reached:**
  - R4 100 times at node size 30;
  - a fix step that grows the tree (`split.space3` inside a fix step) at
    30, though 2,740 times at 8;
  - an empty leaf merged into two nodes, at either size;
  - a `bounds:` error from either writer.
- **Not done (section 8 of the plan):**
  - proofs;
  - restarts and P2;
  - reclaim, eviction and lazy reading over the untidy states;
  - the record's format;
  - Java;
  - the whole model (`Spec`) on MT's transactions.

# 10. The files here

- `report.md`: this report.
- The three Lean files at the branch's last commit:
  - `Mt.lean.txt`;
  - `MtTest.lean.txt`;
  - `MtDeps.lean.txt`.
- `lakefile-stanza.txt`: the program's stanza in `lean/lakefile.toml`.
- `runs/`: the runs' summaries as the program printed them. They are
  T0's, T2's selftests and smoke runs, T4's, T5's `30-*.txt`, T6's
  `8-*.txt` and T5's checks.
- `scripts/`:
  - `deps.txt`, MtDeps' output;
  - `counts.py` and `counts.txt` (C1 to C5);
  - `aggregate.py` and `aggregate.txt` (the totals of sections 2 and 4);
  - `scan-smallest.lean.txt` (section 5).
- `t3-review.md`: T3's review.
- `state.md`: the trial's log, as it stood at T8.
