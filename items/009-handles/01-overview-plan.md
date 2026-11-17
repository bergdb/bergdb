009-01. Overview plan: handles in BergDB
========================================

Created 2026-10-25 by Claude (Opus 5.5, Claude Code) for Frans Lundberg, at
his request ("Yes, create 009-01."), after a discussion of how to go about
the work and how to handle it in Git. Frans: "It is implementing handles
004 in BergDB. This is a major one. [...] 009-01 can be a first overview
plan. Then 02 for the detailed implementation plan when 01 approved."

**Status: approved and carried out.** Frans approved it on 2026-10-25 by
asking for 009-02 ("Go ahead and adjust 01 and then write 02."), which was
to follow "when 01 approved"; his decisions are in section 8. The work ran
from 2026-10-25 to 2026-10-27 ([009-02](02-implementation-plan.md),
section 9; [009-03](03-measurements.md)), and Frans merged the branch on
2026-10-26 (`98981f8`). Section 1, "Where the targets stand", says what
each target came to.


# 1. The goal

Eviction without stop-the-world. Today Level 4 frees memory with a sweep
that walks every resident object, twice, under the write lock
([004-01](../004-indirect-swizzling/01-report.md), 3.2). Its cost grows
with the resident memory, not with what it frees: 0.5 s at a budget of
66 MB, 13.8 s at 2.66 GB, and 266 s during 004-02's load of 100M keys,
with the readers and the writer waiting
([004-02](../004-indirect-swizzling/02-scale-tests.md), 10.5.3). Frans
([004-03](../004-indirect-swizzling/03-summary-and-direction.md), section
1): "The current cache eviction has unacceptable stop-the-world that can
reach 10s of seconds and more. Indirect swizzling is the path forward to
avoid stop-the-world."

009 replaces the sweep with handles, 004's option D (chosen 2026-10-24,
004-03, section 1). A memory pointer of a key node or a top node goes to a
small per-node handle, and the handle goes to the node's one object. To
evict an object, BergDB changes its handle only, and nothing needs to know
who points to it (004-01, section 4).

In the words a user should be able to rely on, once 009 is done:

    Eviction does a bounded amount of work at a time, whatever the size of
    the database and of the cache. No get or commit is stopped for more
    than about 20 ms by BergDB's own code. The garbage collector's pauses
    come on top; with ZGC, or Shenandoah in its default mode, they stay
    small.

Done when:

1. **No walk of the resident set.** The work of an eviction step is
   bounded by a constant, not by the resident memory. `Residents.walk` is
   no longer part of eviction, and the byte count is exact without walks
   (004-01, 4.5).
2. **Pauses.** In P4's soak and in 004-02's runs with eviction (10M keys,
   on F53 and s1), the longest time a get or a commit is stopped by
   BergDB's own code, eviction and the locks a get or a commit waits on, is
   below about 20 ms (Frans, 2026-10-25; 004-04 had about 10 ms). Today:
   up to 266 s. The collector's pauses are the JVM's and not part of the
   target (Frans, 2026-10-27: "The target of 20 ms is for the BergDB code.
   Not for the JVM itself."); the runs use JVM settings that keep them
   small, ZGC or Shenandoah in its default mode ("feel free to chose JVM
   settings to limit the maximum pause time"), and which collector to
   recommend is a separate question (009-04, section 8).
3. **Gets.** In memory, on one thread, within 20 percent of today's
   (Frans, 004-03, section 1; 004-01 measured 9 to 13 percent for the
   hop). With 4 and 8 threads, more gets a second than today, since the
   pointer lock and the stamp leave the fast path (004-01, 3.4). From the
   OS cache and from the device, no difference beyond the noise.
4. **Memory.** Heap bytes per KV (Props, MEM) measured against 2026.1 and
   recorded. Expected from 004-01 (5.4): 3 to 4 percent more for compact
   keys, 12 to 18 percent for random 16-byte keys.
5. **Streams.** Every record the same as 2026.1's: StreamDigest gives
   2026.1's digests on the standard sets (008-01, "How to compare a later
   version"), after every step, not only at the end.
6. **Lean.** The physical layer restated for handles: T-CACHE (any cache
   schedule gives the model's records and D), T-READ (reads give P) and
   T-PIN over the new state, proved; `lake build` with no warnings and no
   `sorry`. The merge waits only for phase 2's model and the
   serialization invariant; the rest follows on `main` after it (G2b).
7. **Gates.** `java/before-commit.sh`, `level1.sh` to `level4.sh`,
   `night.sh`, and the performance suite against 2026.1, the two jars in
   turns on one machine (008-01).
8. **Docs.** docs/levels.md, Level 4; the alignment of Level 4 with
   handles; README.md and docs/levels.md no longer list the sweep among
   the known limits; docs/log.md.

Where the targets stand, 2026-10-28 (the numbers in 009-03, section 0):

1. Met (step 3b). Eviction's batches walk nothing, and `Residents` counts
   the bytes exactly without walks. The test schedules (`VALUES`, `EVERY`,
   `RANDOM`; test-only) still walk, as 009-02 planned for step 3b.
2. Met in P4's soak and the pause probe; not yet with 8 threads at 665
   MB under ZGC ([005-65](../005-todo/65-gets-with-8-readers.md)).
   BergDB's own waits: eviction's batches take at most 2 ms on F53 and 4
   ms on s1, and since [005-46](../005-todo/46-stream-file-lock.md) no get
   waits for the stream's writer, a force, a new file or a cut. P4's soak
   under ZGC on F53, on `main` with 005-46 (006-09's quiet block): the
   longest commit 5.1 ms and the longest read 3.6 ms; the cuts are no
   longer the slowest (before 005-46, 88 to 171 ms; 009-04, section 7.3).
   In the pause probe on s1 a force of 2,500 ms left every get at 12.1 ms
   at most (005-46). 004-02's runs at 10M keys: from the OS cache on F53
   with ZGC the longest get 6.0 ms with up to 4 threads (3.45 ms at step
   3d), but 27 and 36 ms with 8 threads, with readers' loads waiting for
   the eviction thread over 10 ms (`c1f1f15`: 2.1 ms), which 005-65 is to
   explain; from the device on s1 64 to 74 ms, s1's disk, and one get of
   2,760 ms with one reader, no writer and no collection or safepoint
   under it, which Frans accepted as not BergDB's (2026-10-28: the run's
   memory cgroup at its limit, the kernel reclaiming about 56 times a
   second; step 3d's 2,690 ms the same; 009-03, section 9). What is left
   above 20 ms, but for 005-65, is the collector's (G1's pauses, ZGC's
   allocation stalls) and s1's disk; a writer's wait for room in the write
   buffer is the disk's too, and does not count (005-46, decision 5).
   Since 2026-11-06 the 8-thread case is explained and closed (015-86,
   formerly 005-65; Frans): readers off their cores on a full machine, the
   operating system's scheduling, outside the target; with 7 readers on
   F53, 0.4 gets in a million over 10 ms.
3. Met (009-03, section 5): in memory on one thread 3 and 11 percent fewer
   gets (G1, ZGC); with 4 threads 12 and 3 percent more, with 8 threads
   101 and 61 percent more; from the OS cache 1.4 to 4.6 times as many.
4. Recorded (009-03, section 3): MEM 130 bytes per KV (2026.1: 191).
5. Met: StreamDigest gave 2026.1's digests after every step (009's log).
6. Met: `tc_handles`, `tr_handles`, `t2_handles`, `tr_handles_restarts`
   and `tp_handles`, with no warnings and no `sorry` (009's log,
   2026-10-26).
7. Met. The gates at every step and on the merged tree (`night.sh`:
   NIGHT OK on `f4e93d8`). `performance.sh ab` against 2026.1, quick
   suite, on 2026-10-26: gets on one thread 3 to 9 percent fewer, from 4
   threads 19 percent more; again in 006-09's quiet block, on `main`
   (`f9e295d`, 2026-10-28, 01:00): no alerts, throughput 1 to 25 percent
   higher (four reader threads 25 percent, the mixed scenario's gets 17
   percent), startup 2 to 4 percent faster; the only flags are G1's pause
   maxima, 24 to 39 ms in r-1k-fin (005-46, "Confirmed in the quiet
   block").
8. Met: docs/levels.md, section 7; 009-05; README.md's Level 4 row;
   docs/log.md (2026-10-26).

Not in 009:

* **005-38, writes at scale.** Investigated on 009's branch once eviction
  runs without the sweep, before the Lean proofs are final (step 3e), as
  004-03 says (2.4, point 4). A fix is work of its own.
* **A background evictor.** Eviction stays where it is today: in bounded
  batches under the write lock, at transaction boundaries and after loads
  (004-01, 4.5). A thread of its own needs a pin check made atomic with
  the writer's marking. Later.
* **The collector.** G1 runs full collections under eviction, with
  handles or without (004-04). 009 measures with ZGC and Shenandoah, and
  the docs say that the 20 ms target needs one of them. Node contents kept
  out of the Java heap would be another item.
* **The cold-cache startup** (`DbStarter.linkD`, one header read per
  pointer of D; 004-02, 10.5.8). With handles, linkD resolves D's
  pointers to handles by id (004-01, 4.7). 009 must not make startup
  slower, and measures it.
* **Option C**, a forest of single-owner pointers, or direct pointers in
  the top levels of the current tree beside handles below them (004-01,
  8.3): only if gets miss target 3, and then as Frans decides.


# 2. Where 009 starts

* **The design sketch:** 004-01, section 4: the handle and the pointer,
  reading, the writer, records, eviction, values, startup, concurrency,
  the Lean model, and what the change touches. 009-02 turns it into a
  design.
* **The table from node id to handle**, which must grow without
  stop-the-world: open, 004-03, section 3.
* **The collector:** 004-04. Under eviction only ZGC and generational
  Shenandoah meet the 20 ms target; G1 paused up to 58 ms even with a
  10 ms pause goal. Their cost: 30 percent more heap per key with ZGC,
  3 percent with Shenandoah, and 10 to 13 percent fewer gets in memory on
  one thread.
* **The baseline:** release 2026.1 (item 008): its runs, and its jar to
  run beside 009's.
* **The size of the change.** Java (004-01, 4.10): KeyNode, TopNode,
  NodeCollection, Cache3, Dag, `resolvePointers`, DbStarter, Eviction,
  Residents, Audit, PointerLocks, their tests, and the four level scripts.
  Lean: today's eviction files, `Evict*.lean` with their proofs, are
  11,695 lines, and the physical layer's `Phys*.lean` 8,798
  (2026-10-25); the checker's C-P too. The stream format and the records
  do not change.


# 3. The approach

Three things shape the plan.

**Records do not change.** A pointer's serialized reference is decided by
the pointer and its handle, never by what reads left in memory (004-01,
4.4). So StreamDigest must give the same digests after every step. That
is a strong test of the writer's side, and it lets most of the work be
ordinary commits on `main`.

**Most of the work on `main`; the switch on a branch.** Steps that keep
today's behaviour go on `main`, gated as usual: tools, the new table, the
read path where it can change without handles. The switch of the pointers
to handles and the removal of the sweep cannot be half done. They go on a
branch, `009-handles`, merged into `main` once, at the end (section 6).

**The Lean model first; the proofs once the Java design has settled.**
The model of handles (its state, operations, invariants, and the
theorems' statements) is written early, on `main`, in new files beside
today's physical layer, as 004-01 recommends (8.4): it checks the design
before the Java is written. The proofs follow once the design has settled
on the branch and 005-38 has been investigated. Lean never depends on code
that is only on the branch.


# 4. The phases

## Phase 0. The design: 009-02

The detailed implementation plan, 009-02, written once this plan is
approved. It settles what 004 left open, with the small measurements
they need:

* **The table** from node id to handle (004-03, section 3): many HashMaps
  (Frans: "Just having 4096 HashMaps to start with is not such a bad idea
  either. It is simple, and I understand it."), linear hashing, or
  incremental rehashing. First the measurements: the pause of a resize
  with 4,096 maps at 1M to 100M resident nodes, and the bytes per entry
  of each option.
* **The policy:** CLOCK over the table, or a random choice into a cooling
  FIFO (LeanStore); and where recency lives: a bit in the handle, written
  only when it is clear, in place of today's stamp in `pos[i]`.
* **The handle:** a new class, or Cache3's `CacheEntry` turned into it;
  with the node id or without (32 or 24 bytes, 004-01, 4.1). Values keep
  direct pointers and are charged to their leaf (4.6).
* **The Java Memory Model, and the reader protocol.** First a study of
  the JMM (JLS chapter 17; volatile and final fields, the VarHandle access
  modes, safe publication) and of how today's code publishes the writer's
  work to readers (`readSync`, the nodes' sizes, PointerLocks). Then the
  protocol: the lock-free fast path, for resident nodes only, and the slow
  paths (resolve, load, install, promote, evict), which may take locks: a
  read from the stream costs far more than a lock (Frans, 2026-10-25).
  Written down field by field, with the barrier that publishes each write
  to the readers, before any code. 004-01 (8.1) asks for its own check of
  Q8: an unswizzle may race a lock-free read. Related: 005-07, BergDB's
  synchronization never reviewed as a whole.
* **The steps** of phases 1 to 6 in detail: their order, which of them
  pass the gates alone, and the tests of each.

* Done when: Frans approves 009-02.
* Size: M. The measurements run in the background on a quiet F53.

## Phase 1. Preparation on `main`

Today's behaviour kept and every record the same; each step a commit,
with `before-commit.sh` and StreamDigest:

* **1a. A pause probe.** A stress test in `java/stress/` that measures the
  longest stop of a get and of a commit under eviction, and how much of it
  is eviction and how much the collector. Run on today's code with G1 and
  ZGC: the numbers before 009, beside 2026.1's. Also, ScaleBench's reads
  of internals that handles change (008-01: the eviction's figures, the
  resident bytes, the load listener) behind a small interface, so that
  phase 5 runs one workload on both jars.
* **1b. The table.** The table chosen in 009-02 replaces Cache3's 256
  HashMaps, with today's entries in it; the pause probe measures its
  resize. `CacheEntry`'s `refCount`, never decremented, goes (004-01,
  section 9).
* **1c. The read path, as far as it can change without handles.** The
  shared counter of every get (`aux.getOpCount`); and `readSync` on the
  get path, which today publishes the writer's work to the readers (the
  database's state, reclaim's `firstAvailablePos`, the super root). It can
  leave the get path only with another barrier in its place, for example
  a volatile read of the super root, which the writer sets with a volatile
  write after the transaction (009-02). The pointer lock and the stamp
  stay until phase 3: today's eviction relies on them.
* **1d. Seams, where they make the branch smaller.** The follow, install
  and evict operations of NodeCollection and Cache3 behind methods whose
  bodies phase 3 replaces and whose callers stay.

* Done when: each step gated; the pause probe's numbers before 009 in
  this item.
* Size: M.

## Phase 2. The Lean model of handles, on `main`

In new files beside today's physical layer, for example
`lean/SIS/Handle.lean`, `lean/SIS/HandleExample.lean` and
`lean/SIS/Proof/Handle*.lean`. Today's `Phys*` and `Evict*` files do not
change.

* **The state** of 004-01 (4.9): a table from node id to a handle (an
  object or none, the written position, dead or not); per object, per
  pointee, a reference and whether it is resolved. **The operations:**
  follow (resolve and install), the writer's promote, write, evict,
  re-resolve, and startup's rule 4.
* **The invariants:** one live handle per node, and one object per live
  handle; an object is canonical with its node's whole history or an exact
  version (CC, INV-CAN, INV-SNAP); the serialization invariant of 004-01
  (4.4) in place of INV-SLOT's two halves.
* **The theorems' statements:** T-CACHE, T-READ and T-PIN over the new
  state, reusing lemma M (`LM_newer`, `LM_ruleR`) and the Level 2 and 3
  theorems. Run as an executable model with `#guard`s, as
  `EvictExample.lean` does.
* **The first proof:** the serialization invariant, on which "records do
  not change" rests.

* Done when: the model and its examples, and the serialization invariant
  proved; `lake build` with no warnings and no `sorry`; lean/README.md
  lists the new files as work in progress.
* Size: M to L. Beside phase 1.

## Phase 3. The switch, on the branch `009-handles`

In the branch's worktree (section 6), in steps:

* **3a. Handles for index nodes.** Pointers of key nodes and top nodes to
  handles: KeyNode, TopNode, NodeCollection's followers, Dag (a new
  pointer to a node takes its handle), `resolvePointers` (the rule of
  004-01, 4.4), and DbStarter's rule 4.
* **3b. Eviction by handles.** The policy of 009-02, in bounded batches;
  Eviction and Residents rewritten without walks, with exact accounting;
  values with their leaf; the sweep deleted.
* **3c. The read path.** PointerLocks and the stamp off the fast path, for
  resident nodes, with 009-02's barriers. The slow path, which reads the
  stream, may keep a lock.
* **3d. The audit and the tests.** Audit checks phase 2's invariants in
  Java: one live handle per id, and the serialization invariant on every
  record written in the tests. EvictionInvariance, EvictionReaderTester
  and `level4.sh` for handles.
* **3e. 005-38's investigation**, with the sweep gone (004-03, 2.4, point
  4): how much of the slow loads was the sweep, and what a fix of the
  write path would change in what is pinned or written.

* Done when: all gates pass on the branch (`before-commit.sh`, `level1.sh`
  to `level4.sh`, `night.sh`), and StreamDigest gives 2026.1's digests.
* Size: L.

## Phase 4. Lean: the proofs and the alignment

* The proofs of T-CACHE, T-READ and T-PIN over handles, in phase 2's
  files, on `main`. The checker's C-P for the new state, and Java's trace
  exporter (on the branch) if the traces change.
* The alignment of Level 4 with handles: the mapping of Java's state to
  the model, and the register, as level4-alignment.md does for today's
  code. A new document or a new version of that one: for 009-02.

* Done when: the proofs and the alignment, after the merge (G2b). 009 is
  done when they are.
* Size: L, the largest phase: today's eviction proofs are 11,695 lines,
  though 004-01 (4.9) expects simpler statements.

## Phase 5. Measure and accept

Targets 2 to 4 of section 1, 009's jar against 2026.1's, in turns on one
machine (008-01): J10's gets; gets from 2, 4 and 8 threads; P4's soak with
eviction; LargerThanMemory; ScaleBench at 10M keys on F53 and s1; each
with G1, ZGC and generational Shenandoah (004-04's `run2.sh`); the pause
probe of 1a; Props for MEM; the cold-cache startup.

* If gets miss target 3: the combination of 004-01 (8.3), direct pointers
  in the top levels of the current tree, for Frans to decide.
* Done when: the results in this item, and Frans's go for the merge.
* Size: M, in the background, with F53 quiet and s1 to itself.

## Phase 6. The merge

* `git merge --no-ff 009-handles` into `main`, after the gates on the
  merged tree.
* Lean (G2b): phase 2's model and the serialization invariant proved;
  lean/README.md and docs/levels.md say which theorems over handles are
  still to prove. Today's eviction files stay until phase 4's proofs
  replace them, and then go; Git keeps them.
* docs/levels.md, Level 4; README.md's known limits; docs/log.md; 004
  done, with a link to 009; this item's log, and its outcome once phase 4
  is done.

* Size: S.


# 5. Order

* Phase 0 first.
* Phases 1 and 2 side by side.
* Phase 3 after phase 1, whose table, pause probe and seams it uses, and
  after phase 2's model, which checks the design that phase 3 implements.
* Phase 4's proofs once phase 3 has settled the design and step 3e is
  done; phase 5 beside them.
* Phase 6 after phase 5 and phase 2's serialization invariant (G2b).
  Phase 4's other proofs go on after the merge; 009 is done when they
  are.


# 6. Git

Decided (Frans, 2026-10-25, 12:54: "As proposed."; and G1a, 13:09: "Push
the commits."):

* **Work that keeps today's behaviour goes on `main`**, as ordinary gated
  commits: phases 1 and 2, phase 4's Lean, and every fix made while 009
  runs.
* **The switch goes on a branch, `009-handles`**, made from `main` when
  phase 3 starts. It lives in a worktree of its own (`git worktree add
  ../bergdb-009 009-handles`, beside the main tree): several sessions share
  the main tree, so nobody checks the branch out there. One session at a
  time works in the worktree; others use scratch clones of the branch.
* **`main` is merged into the branch often, not rebased onto:** after every
  commit on `main` that touches `java/src/bergdb/core` or
  `java/src/bergdb/dag`, and at least once a week.
* **Commits on the branch:** the session working on it commits at each
  step whose gates pass (`before-commit.sh`, and StreamDigest as 2026.1's),
  in Frans's name, without asking each time: uncommitted work in a
  worktree is easily lost. Frans decides the merge into `main`.
* **The merge:** one `git merge --no-ff 009-handles`, once all the gates
  pass on the merged tree. `git log --first-parent main` then reads as one
  line, as today's history does, and the branch's commits stay for
  `git bisect`.
* **While the branch is open,** `main` takes no changes to what the branch
  rewrites (Eviction, Residents, Cache3, NodeCollection's followers,
  PointerLocks) except fixes, which are then merged into the branch.
  007-03's steps 2 to 5, the take, can go on `main`. 005-38 goes on the
  branch (step 3e) or after the merge.
* **Pushed:** the branch's commits go to `origin`
  (github.com/bergdb/bergdb) after each commit (G1a), a copy off F53.
* **On `main`, unattended:** the session commits each gated step of phases
  1 and 2 in Frans's name and pushes `main` (Frans, 2026-10-25, 19:40).


# 7. Risks

* **The handle's lifecycle.** Dead handles, re-resolution, one live handle
  per id, and the races between a reader's install, the writer's promote
  and an eviction. Against it: phase 2's model before phase 3's code, the
  audit (3d), and the reader tests under eviction.
* **Lock-free reads.** Hard to get right. A reader that takes no lock
  must still see all that the writer published before it: a node's
  arrays, a new handle, an installed object, and never half of them. The
  Java Memory Model gives that only through a happens-before edge: a
  release write by the writer after its writes (a volatile write, or a
  VarHandle `setRelease`), and an acquire read by the reader before its
  reads (a volatile read, or `getAcquire`). Against it: the study of the
  JMM and the protocol of 009-02, with the barrier of every field written
  down and reviewed before the code; jcstress tests of the protocol;
  tests with many readers under eviction. And lock-free reads only where
  they pay: on the fast path, when the nodes are resident. A read from the
  OS cache takes microseconds, from the device 0.1 to 0.9 ms (004-02,
  10.5.2), and an uncontended lock tens of nanoseconds, so the slow paths
  may lock (Frans, 2026-10-25).
* **The cost of a hop.** A scattered handle costs much more out of cache
  (874 against 583 ns; 004-01, 5.1), and ZGC keeps handles where they were
  allocated (004-02, 10.3). Against it: a handle allocated with its object
  at a load; phase 5 measures under ZGC; the combination of 004-01 (8.3)
  as the fallback.
* **Memory.** 24 to 32 bytes a handle, and dead handles that parents keep
  until they are followed or evicted (004-01, 4.5). Phase 5 measures it
  (target 4).
* **Drift.** A branch open for long drifts from `main`. Against it: phases
  1 and 2 on `main`, so that the branch holds only the switch; frequent
  merges of `main` into it; the rule of section 6 on what `main` does not
  touch.
* **Lean's size.** The proofs are the largest part and may come long after
  the Java. With G2b the merge waits only for phase 2's model and the
  serialization invariant.


# 8. Decisions

Decided:

* Handles (option D) for eviction without stop-the-world: Frans,
  2026-10-24 (004-03, section 1).
* The work after release 2026.1: Frans, 2026-10-25 ("Planning now.
  Execution after release 008.").
* Item 009, with 009-01, this overview plan, and 009-02, the detailed
  plan, once 009-01 is approved: Frans, 2026-10-25.
* Git, section 6: Frans, 2026-10-25 ("As proposed.").
* The phases, section 4: Frans, 2026-10-25 ("Phases are good.").
* The pause target, about 20 ms: Frans, 2026-10-25 ("Increase the target
  max pause time from 10 to 20 ms.").
* Lock-free reads on the fast path only, for resident nodes; the slow
  paths may lock: Frans, 2026-10-25 ("Lock-free reads are for when all
  nodes are cached in memory. If we read from disk, locks are relatively
  cheap compare to the time to read from disk.").
* **G1. Push the branch to `origin`** (github.com/bergdb/bergdb): G1a,
  after each commit (Frans, 2026-10-25, 13:09: "Push the commits.").
  * G1a. Push `009-handles` after each commit, or once a day: a copy off
    F53, and the work visible on GitHub before the merge.
  * G1b. Keep it local: nothing of 009's branch leaves F53 until the
    merge, when `main` is pushed as usual.
* **G2. What the merge waits for in Lean:** G2b (Frans, 2026-10-25,
  13:09: "G2b.").
  * G2a. All of phase 4: T-CACHE, T-READ and T-PIN proved over handles,
    and the alignment written, before the merge. `main` then always has a
    proved model of the Java it holds, as in item 001, where Level 4's
    model (E1 to E6) came before its Java (J1 to J10). The merge may wait
    long after phase 5.
  * G2b. Phase 2's model and the serialization invariant proved (so that
    "records do not change" is proved, besides StreamDigest), and all of
    Java's gates; the rest of the proofs on `main` after the merge, with
    lean/README.md and docs/levels.md saying which theorems are pending.
    Eviction without stop-the-world reaches `main` sooner; between the
    merge and the proofs, Level 4's proofs are for the old design.
  * Proposed, and decided: G2b. The serialization invariant is the proof
    that de-risks the most: it is what keeps the stream right. The rest
    proves that eviction never changes what reads give, which the reader
    tests and EvictionInvariance check in the meantime.

Decided with 009-02:

* **G3. Phase 0's choices** (the table, the policy, the handle, the
  protocol): proposed in 009-02, and decided with its approval. Decided
  2026-10-25, 19:10: T1a, T2a, T4b, T5a, T6b (as 009-02, 3.4, argues),
  T7a; T3a at 19:34.


# 9. How to work

As for the other items: Java and Lean changes made and gated in a scratch
clone (for `main`) or in the branch's worktree, and copied into the tree
last, with the gates run again on the combined tree. Timing runs on a
quiet F53 (no other session's gates or JVMs), and on s1 when nothing else
runs there. On `main`, Frans commits, or the session he asks to; on the
branch, as section 6 says.
