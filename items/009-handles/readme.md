009-handles
===========

Created 2026-10-25 by Frans Lundberg. Status: open.

Handles in BergDB: memory pointers of index nodes that go through a
per-node handle, so that eviction does bounded, local work and BergDB has
no stop-the-world of its own. The implementation of item 004's direction
([004-03](../004-indirect-swizzling/03-summary-and-direction.md)): the
plan, the work on `main` and on the branch `009-handles`, the measurements
and the outcome.


Files
=====

* [01-overview-plan.md](01-overview-plan.md). 009-01, the overview plan:
  the goal and what "done" means, the phases (the design, preparation on
  `main`, the Lean model, the switch on the branch, the proofs, the
  measurements, the merge), Git, the risks, and the decisions for Frans.

* [02-implementation-plan.md](02-implementation-plan.md). 009-02, the
  implementation plan, phase 0's output: BergDB today where 009 changes
  it, the Java Memory Model and the fast path's barriers field by field,
  the design (the handle, pointers, the table, following, the writer,
  records, eviction, values, startup, the audit), the steps of phases 1
  to 6, decisions T1 to T7 for Frans, and the measurements of the table.
  TableBench, its script and outputs are in
  [02-implementation-plan/](02-implementation-plan/). Section 9 records
  what the implementation changed from the plan, and why.

* [03-measurements.md](03-measurements.md). 009-03, the measurements of
  phases 3 and 5: the pause probe on s1 and F53, jcstress, MEM, ScaleBench,
  against 2026.1 in turns. Outputs and scripts in
  [03-measurements/](03-measurements/).


Log
===

2026-10-25. Created the item, at Frans's request ("Let's discuss a major
piece of work. Planning now. Execution after release 008. It is
implementing handles 004 in BergDB. [...] We should create a new item for
this. 009 i think. 009-01 can be a first overview plan. Then 02 for the
detailed implementation plan when 01 approved."), with 009-01 drafted by
Claude (Opus 5.5, Claude Code). Git as Claude proposed (Frans: "As
proposed."): the switch on a branch `009-handles` in a worktree of its
own, everything else on `main`, one `--no-ff` merge at the end.

2026-10-25, 13:09. Frans on 009-01: "G2b. Push the commits. Phases are
good." G2b (the merge waits for phase 2's model and the serialization
invariant only) and G1a (the branch's commits pushed to `origin`) recorded
in 009-01; the rest of 009-01 waits for his reading.

2026-10-25, 13:25. Frans's comments on 009-01, applied: headings with `#`
(a setext heading that starts with a number renders as a list item); the
pause target from 10 to 20 ms; lock-free reads are hard, need a barrier
for every write published to the readers and a study of the Java Memory
Model, and are for resident nodes only, as a read from disk costs far
more than a lock. Then: "Go ahead and adjust 01 and then write 02."

2026-10-25, 15:55 to 16:25. 009-02 written by Claude (Opus 5.5, Claude
Code), at Frans's request ("Go ahead and adjust 01 and then write 02."),
after release 2026.1's quiet block on F53. TableBench run 16:11 to 16:14:
4,096 maps stop one map for 0.23 ms at 30M entries under ZGC, today's 256
maps for 11.6 ms. 009-02 waits for Frans's approval and his decisions T1
to T7.

2026-10-25, 19:10. Frans on 009-02: "I decide: T1a, T2a." "I decide: T4b,
T5a." "T6. Use T6b if you argue it is safe." "I decide: T7a." And T3:
"Please expand and explain the options more. Pros and cons with T3a and
T3b. Why did you propose T3a?" Recorded in 009-02 by Claude: the
decisions; section 3.4, the argument that a plain read of a pointer to a
handle is safe (T6b; a pointer to a value keeps an acquire read); T3
expanded (what needs the id, when dead handles are followed, pros and
cons, why T3a, a variant T3c); and the counting of handles' memory, dead
handles included (4.7, open point 8). T3 is open.

2026-10-25, 19:34. Frans: "I decide T3a. T4b, Pointee is a good name."
009-02's decisions are complete.

2026-10-25, 19:40. Frans's answers before the unattended work: commit each
gated step on `main` in his name and push `main`; go through phase 1 and
Lean's 2a to 2c and on into phase 3a on the branch; a pointer to a value
keeps its acquire read (009-02, 3.4, point 5); timing runs on F53 when it
is quiet, and on s1.

2026-10-25, 19:55. Frans: BergDB moves to `--release 17` ("Move to
--release 17. Code compiles for that. But we will test performance on the
latest jvm."), as 02's VarHandle needs Java 9 or later; step 1-0 in 02.

2026-10-25, 20:07. Frans: "I want you to work on the 009 implementation
until completion. Work unattended through the night. I will have a look at
your work in the morning; Monday morning." Claude works on in this
session; the merge into `main` (phase 6) waits for Frans's go, as section
6 of 009-01 says.

2026-10-25, 20:14. Relayed by the session that monitors this one (f1-40),
Frans's words to it: "If Phases 1-3 are successful, I want the Handles
session to continue with Phases 4, 5, 6." Read as: phases 1 to 3 each
through their gates first; the merge (phase 6) only if phase 5 meets
targets 2 to 4 of 009-01 and 02d (the serialization invariant, G2b) is
proved; otherwise stop before it, with the results in this item, for
Frans to decide.

2026-10-25, 19:55 to 21:20. Phase 1 on `main`, each step with
`before-commit.sh` and StreamDigest as 2026.1's (36 of 36): 1-0
(`--release 17`), 1a (PauseProbe, CacheStats), 1b (4,096 maps, a lock each,
CacheEntry gone: MEM 174 bytes per KV, 2026.1 191), 1c (reads without the
`readSync` monitor; `level4.sh quick` OK), 1d (seams). The branch
`009-handles` made from `main` after 1d, in the worktree `../bergdb-009`,
and pushed. Step 3a on the branch (`4e66a59`): handles, with the followers
still under the pointer locks and the controller still walking;
`level4.sh quick` OK, C-P 0 of 2643. Phase 2's model (2a to 2c, and 2d
started) on `main` (`74af34c`). The model's runs found two things 02 did not
say (Handle.lean's header, choices 1 and 7): a pointer resolved again from a
dead handle must keep the position the node was last written at, and the
slow path must compare with it. Java does both pointer-locally: the slow path
takes the newer of the pointer's reference after Rule R and its dead
handle's written position, and writes it back into the pointer (record
neutral); the model is being aligned with that. The runs also settled open
points 1 and 2 of 02 (the fast path's test with `pos[i]` is enough) and
asked for an explicit vpos case where Java compares references (open point
3; `Spos.newer`). Step 1a's timing runs (2026.1 and `main`, G1 and ZGC) wait
for a quiet machine.

2026-10-25, 21:20 to 21:50. Step 3c on the branch (`19a8c58`): the
lock-free fast path; the pointer locks off every follower; the release
store of a pointer's change, paired with the acquire read of a pointer to
a value. jcstress tests of the barriers (`java/stress/jcstress/`, a tool,
not a gate): on F53, no forbidden outcome in 1.0 to 1.7 billion samples a
test, while the control without an edge showed its race 166,641 times in
5.1 billion (log in 03-measurements/). The pause probe on s1 (1M keys, two
readers, 2026.1, `main` at 1d and the branch at 3c, G1 and ZGC, budgets of
20 and 100 MB) in 03-measurements: 2026.1's sweeps stop gets and commits
for 0.7 to 2.5 s; at 3c no batch stops a get, but commits waited for the
eviction thread, batches took up to 100 ms, and the resident bytes went
above the budget. Step 3d's changes come from these runs and its tests.

2026-10-25, 21:50 to 22:40. Step 3d on the branch, in two commits. The
first (`7831909`): the audit's handle checks, EvictionReaderTester's
f-tests with 8 readers and under the capacity controller, two more
ReclaimReaders runs in `level4.sh`, and the pointer locks removed. The new
tests found two faults of steps 3a to 3c, both fixed: an eviction read a
handle's object before its compareAndSet, so a dead handle could keep an
object; and a reader's swizzle could replace the writer's newer handle in
a pointer, or its write-back lower a reference, so that a later follow
read an older version (stale reads, 2 runs of 9). And s1's runs found two
more: the eviction thread kept the writer out of the write lock, and the
values that reads load into pinned leaves stayed. `level4.sh` in full OK
(C-P 0 of 7917). The second (`66c8f3a`): batches bounded to 2 ms, the
trigger from the pinned bytes the hand counts, and loads that wait up to
2 ms when eviction falls behind; s1's probe at 20 MB under G1: 645,083
commits a minute (3c: 2,583; 2026.1: 221,900), 41 MB resident at the end
(3c: 138 MB). jcstress on s1 (x86): no forbidden outcome. MEM: 130 bytes
per KV (2026.1: 191). The details are in 02's section 9 and in 009-03.
s1's longest waits of a get or a commit at step 3d, 1.4 and 2.7 s, have no
collection or safepoint under them: a reader's read of the stream file
waits for the writer's append and its `fsync` (FileStream.DbFile, one
monitor for both), on s1's slow disk; not eviction, and for 3e.

2026-10-25, 22:41 to 2026-10-26, 00:30. Phase 5's first runs, the branch at
step 3d against 2026.1 in turns (009-03, sections 0 and 4 to 8): s1's pause
probe and ScaleBench at 10M keys (the load with a 600 MB budget, then from
the device at 133 MB, G1 and ZGC); F53's timed block, 22:55 to 23:52, with
the Lean session paused (Props, the pause probe with G1, ZGC and
Shenandoah, and 2026.1's ScaleBench block for each jar). Target 2 met with
ZGC on F53 (the longest get from the OS cache at 10M keys 3.45 ms, 2026.1
7.3 s); target 3 met (one thread in memory 3 and 11 percent fewer gets, 8
threads 101 and 61 percent more); target 4 recorded (MEM 130, 2026.1 191).
Step 3e: the 10M load on s1 took 767 s, 2026.1 3,015 s, of which its sweeps
were 119 s and most of the rest reading back what they evicted (25.9 GB
from the device, the branch 4.6 GB). On s1 the longest waits left are the
device's and a reader's wait for the writer's `fsync` (FileStream, for the
stream layer: registered as 005-46; the load's finding is in 005-38). Not yet run: P4's soak and ScaleBench under Shenandoah, on
F53 from 05:00. `main` merged into the branch (`a73cd66`) for phase 6's
gates; `night.sh` runs on it.

2026-10-26, 00:01. Step 2d done, by a Claude subagent working for this
session: T-CACHE over handles is proved (`tc_handles`, `TC_handles_records`;
lean/SIS/Proof/Handle*.lean, about 8,760 lines): from the startup with
handles from R(0), with any reads and evictions between transactions and no
restart, the physical writer with handles appends exactly the model's
records and leaves the model's D, and the memory keeps the invariants of
`TC_handles`. The model was first aligned with Java's step 3a (the written
position travels in the pointer: only an eviction sets it, and the slow path
raises the reference and writes it back). Checked in this session: the
handle modules rebuilt from scratch with no warnings and no `sorry`, and
`#print axioms tc_handles` gives only Lean's standard axioms. On `main` as
`38586b3`. G2b's condition for the merge (phase 2's model and the
serialization invariant) is met. Phase 4a (T2-C, T-READ and T-PIN over
handles) started in the same way. The model's follow is one atomic step, so
the interleavings of Java's slow path are argued in 02, section 9 (the
reads of `writtenPos`).

2026-10-26, 00:20. Step 4b: docs/handles-alignment.md, the mapping of
Java's state with handles to the model's (SIS/Handle.lean) and the register
of where they differ, as docs/level4-alignment.md does for the design
before handles. Written by Claude (Opus 5.5, Claude Code).

2026-10-26, 01:13. Phase 4a done, by the same subagent: T-READ, T2-C,
T-READ with restarts and T-PIN over handles are proved (`tr_handles`,
`t2_handles`, `tr_handles_restarts`, `tp_handles`; SIS/Proof/HandleHist,
HandleHistTrans, HandleReadT, HandleRestart, HandlePin, about 1,980 lines),
mirroring E4 to E6. Checked here: the whole Lean project rebuilt from
nothing (161 jobs, no warnings, no `sorry`), and `#print axioms` for the
five handle theorems and the four of the design before them gives only
Lean's standard axioms. On `main` as `059d741`. Left of phase 4: 4c, the
checker's C-P over the handle state (TraceExport's export of it, and the
model's handle invariants checked on Java's states), and then the removal
of the Phys and Evict files that only the design before handles uses, for
Frans to decide when; and the night runs on the merged tree.
