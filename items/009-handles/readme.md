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
  [02-implementation-plan/](02-implementation-plan/).


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
