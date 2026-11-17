005-04. The A6 failures: is anything to be done?
================================================

Status: done (2026-10-19; see Outcome; its two proposals 2026-10-20, see
Follow-up). Kind: decide. Created 2026-10-19.


Background
----------

A6 ("no adoption") is an assumption that item 001's plan made about Java's
runs: a pointee of a node that is not its live child is a data node or not
reachable. It fails in 5 of 68,901 Java-tier transactions. All five are one
kind: a transaction creates the root of the next key segment's tree and
splits it in place (`Dag.spaceSplitInPlace`), so the segment leaf's earlier
klong of the same transaction, to the split node, becomes a dead pointer to
a node that is still below the leaf.

The proofs never used A6. They use a weaker form, A6', which allows exactly
this case, and A-COPY. Both hold in every Java transaction checked, and
Frans accepted this at K1 (2026-10-17). See
[03-k1-review.md](../001-lean-model-levels-3-4/03-k1-review.md), sections 1
and 3, and [level4-alignment.md](../001-lean-model-levels-3-4/08-level4-alignment.md), section 4.

So nothing is broken. The question is whether to leave it, or tidy up.


Options
-------

1. **Leave it.** A6 is the plan's word for a stronger property than needed;
   A6' is what the proofs need, and it holds. Only record that A6 is no
   longer a target (perhaps drop it from the Java tier's report, so "A6
   fails" stops looking like a failure).
2. **Change Java so A6 holds**: make the in-place split not leave a dead
   pointer in the same transaction (for instance split before the leaf's
   klong is written, or rewrite that klong). Then the model could assume the
   simpler A6. Cost: the records of such transactions change (the format
   stays, but StreamDigest differs from R8's), and Level 2's alignment and
   the conformance sets must be rerun; gain: a simpler assumption.
3. **Prove the assumptions for Java's algorithm.** TREE, A6' and A-COPY are
   checked on Java's runs, not proved. The model has `javaTest`, Java's
   algorithm with marking; proving that its runs meet TREE, A6' and A-COPY
   would turn three checked assumptions into theorems. This is the
   substantive version of the question, and it is more work than 1 or 2.
4. **Look for more kinds.** Only one kind of A6 failure has been seen. A
   short look at whether any other code path can adopt (with larger node
   sizes, reclaim's rewrites, eviction's reloads) would make option 1 safer.


Proposal
--------

Option 1 with option 4's short look now; option 3 as a candidate for later,
together with T-SCHEME (item 001's R6, also checked, not proved), if proving
the remaining checked assumptions becomes a goal (it would matter for a
publication, 005-06). Option 2 is not worth changing the records.


Done when
---------

Frans decides; the decision is recorded here and, if it changes anything,
in `level4-alignment.md`.


First step
----------

Read section 4 of level4-alignment.md and the Java tier's A6 output, and
search the code for other places where a node can gain a dead pointer to a
node still below it.


Size
----

S for options 1 and 4. Option 3 is M to L.


Outcome
-------

2026-10-19, by Claude (Opus 5.5, Claude Code), at Frans's request ("The
005-04 todo. Do as proposed."). Read at `1f4b637`; runs in a scratch clone
of it. Nothing in `java/`, `lean/` or the gates changed. The tools and their
outputs are in [04-a6-failures/](04-a6-failures/).

**Decision (Frans, 2026-10-19): option 1, with option 4's look now; option 3
for later; not option 2.** A6 is not a target. The assumption stays A6',
with TREE and A-COPY, as K1 accepted (2026-10-17), and A6's failures are not
faults.

**What an A6 failure is.** One kind, in two steps.

1. A transaction makes a segment root: the root of a new key segment
   (`Dag.setNode`), or the new root above a split segment root
   (space-split-2). In the same transaction the segment root fills and is
   split in place (`Dag.spaceSplitInPlace`, the parent a segment leaf): the
   node keeps the first half, under a new root, and the segment leaf gets a
   klong with the same compare value to the new root. The leaf's earlier
   klong of the same transaction, to the split node, stays: a dead pointer
   to a node that is current and below the leaf. If the leaf is full and is
   split in space to make room, both klongs go to the half that takes the
   compare value (`KeyNode.firstAndSecond` copies the live klongs, the earlier
   one among them, and appends the new one), and the dead pointer is in that
   half; a time split replaces the earlier klong instead (`replaceKlong`).
2. A6 keeps failing in later transactions while the dead pointer is in the
   leaf and the split node is current: until a split of the leaf drops the
   pointer (a last version copies only live klongs) or the node stops being
   current. Seed 2's four failures, T26 to T29, are one such pointer.

No lookup ever reads the dead klong: a lookup at the transaction's time or
later takes the later klong for the compare value, an earlier lookup sees
neither. It costs one klong and its pointer in each version of the leaf until
a split drops it. For the model it is a pointee like any other: Rule A keeps
the leaf in D while the split node is in D, case 2 of
[level4-alignment.md, 5.4](../001-lean-model-levels-3-4/08-level4-alignment.md), the case that
needs A6' rather than A6.

**Option 4, the code.** Can anything else adopt, that is, give a node
reachable at i a dead pointer to an index node reachable at i?

* At runtime only `Dag.putKv` adds, removes or changes klongs. User
  transactions, reclaim's rewrites (`Reclaim` puts live values again) and
  the startup's rerun (`DbStarter`) all use it. Reclaim's touch only reads
  (`Db.touchRange`, a `getMany` with the writer's listener). Eviction, reloads
  and the startup's links change only the form of a pointer, memory or
  stream, and which object holds a node (`setPointer` in `Eviction`,
  `NodeCollection`, `DbStarter`); they never change a klong, so never P.
* A delete never makes a pointer to an index node dead. A delete klong
  deletes the klongs whose compare value is the key's last segment, of
  length 0 to 6, and they point to value nodes; a pointer to a segment root
  has a compare value of length 7 (`Keys.toSegments`, `Klong`). The public
  API makes every key with `Keys.toSegments`.
* So a pointer to an index node becomes dead only when its node, or the half
  of it that a space split makes (`firstAndSecond`), gets a later key klong
  with the same compare value. The places that add one:
  time-split-1, space-split-1 and space-split-2 (`timeSplit`, `spaceSplit`)
  replace a node that existed before the transaction; it stops being
  current and was reachable only through this parent (TREE), so it is not
  reachable at i. The in-place split of a segment root is the kind above.
  The other in-place splits add no such klong: a time split in place adds
  none to the parent, and a space split in place under an internal node adds
  one for the second half, whose compare value lies inside the node's range,
  where the parent has no klong. `Dag.setNode` adds a klong only when the
  leaf has no live one for the compare value. A value klong that replaces
  another leaves a dead pointer to a value node, which A6 allows.
* Top nodes: a new super root's skip pointers name older top nodes, which
  are not reachable at i; a second new root in the same transaction
  overwrites the super root's root pointer (`TopDs.newSuperRoot`).
* The node size only changes how often the kind occurs: a segment root must
  get more than about half a node of keys in the transaction that makes it.
  The 21 configurations hit it only at node size 8, because their
  transactions are small; a transaction that puts many keys under a new key
  segment, a bulk import say, hits it at any node size.

The kind keeps A6': the split node stays below the leaf's live klong for that
compare value, since a key segment's nodes are reachable only through it,
for as long as the node is current.

**Option 4, by running.**

* The Java tier with a line per A6 failure that says its kind
  ([java-tier.sh](04-a6-failures/java-tier.sh), which applies
  [signature.diff](04-a6-failures/signature.diff) to `A2A3Check2`). On the 21
  configurations of level2-alignment.md, 10.5, the numbers of section 4
  again: 68,901 transactions, A6 fails in 5, A6', TREE and A-COPY in none.
  On seven more, with large transactions and two-segment keys at node sizes
  8, 14, 30 and 62 (3,525 transactions): A6 fails 56 times, at node sizes 8,
  30 and 62; A6', TREE and A-COPY never. All 61 failures are the kind above,
  23 at step 1 and 38 at step 2; none of another kind, none outside the
  leaf's subtree. A small run at node size 8,
  [A6SplitHalf.java](04-a6-failures/A6SplitHalf.java), shows where the dead
  klong goes: with room in the leaf it stays in the leaf; with the leaf full,
  it is in a half that the leaf's split made. Output:
  [java-tier.txt](04-a6-failures/java-tier.txt).
* No trace of the conformance sets had the kind: the checker's A6
  diagnostic was 0 on every set of item 001's final campaign (F1). So the
  records, the restarts and INV-SLOT had never been checked on a transaction
  with it. [traces.sh](04-a6-failures/traces.sh) makes 21 traces that have
  it: conformance.sh's "big" with two-segment keys, at node sizes 8 and 14,
  without eviction and with the random, every and budget schedules. A6
  fails in 24 of their transactions, and every trace is `TRACECHECK OK`:
  C-S, C-R and C-L, and on the 15 with eviction C-P (INV-SLOT, 226,068
  pointers checked) and run E's stream identical to run A's. Output:
  [traces.txt](04-a6-failures/traces.txt).

So A6' holds wherever it was checked, the code has no other way to adopt,
and the one kind does what the model allows, with eviction too. What has not
changed: TREE, A6' and A-COPY are checked on Java's runs and argued from the
code, not proved.

**Option 3, for later.** A correction to its text above: `javaTest` is Rule
A's still-dirty test, not the Dag's algorithm. The model leaves what a
transaction changes abstract (`Spec.exec`; the checker takes Java's changes
from the trace), so TREE, A6' and A-COPY cannot be proved in it for Java. That
needs a Lean model of `Dag.putKv` (key segments, the splits in place and not,
`TopDs.newSuperRoot`) and its alignment with Java: L rather than M to L.

**Proposed** (small; each changes a gate's checks, so the four gates must
pass after it; both done on 2026-10-20, see "Follow-up" below):

1. No gate checks TREE, A6' or A-COPY, K1's open risk 1
   ([03-k1-review.md](../001-lean-model-levels-3-4/03-k1-review.md), section
   7): `level2.sh` step 7 runs `A2A3Check2` on three configurations but
   greps other lines, and the checker's diagnostics do not fail
   `TRACECHECK`. A later change to the splits could break A6' with every gate
   passing. Proposed: step 7 also requires A6' 0, TREE 0 and A-COPY failing
   0, and adds the configuration that has the kind (`-Dmaxnode=8 -Dkeys=1000
   -Dn=50 -Dexact=1 -Dops=40 -Ddel=25 -Dlong=1`, a second); conformance.sh's
   small set gets a configuration like `a6-big` above and its evict set one
   like `a6-random`, so that `level2.sh` (C-S) and `level4.sh` (C-P) check
   the kind in every run.
2. The checker computes A6, not A6' (`adoptionFailures` in
   `lean/Check/Steps.lean`, whose comment still says that E1 decides), so on
   a trace with the kind it reports "A6 (no adoption) fails" and cannot tell
   whether A6' holds. Proposed: the diagnostic computes the model's
   `adoptAt` (A6') instead, and `A2A3Check2`'s summary names A6' as the
   assumption and A6 as information only. This is option 1's "perhaps",
   left undone here: alone it only renames a line of output, and it needs
   the gates as point 1 does.


Follow-up
---------

2026-10-20, by Claude (Opus 5.5, Claude Code), at Frans's request (to "Shall
I do these two now, or add them as a todo entry?": "Yes."): both proposals
above, made and gated in a scratch clone of `1f4b637`, then copied into the
work tree. Frans committed it with 005-10's removal of unused code, in
`3fdf88b`.

1. **The Java tier.** `A2A3Check2` reports A6', TREE and A-COPY as the
   model's assumptions, each with its failures, and A6's failures only as
   information: "adopted index nodes not below the old parent 0
   (transactions 0); below it, which A6' allows and A6, not assumed, does
   not (bergdb 005-04), 1 (transactions 1)". `level2.sh` step 7 fails unless
   TREE, A6' and A-COPY hold on its three configurations, and prints the
   adoptions below the old parent. No configuration was added: step 7's
   second is the one with the kind (seed 4), which point 1 above missed.
2. **The checker.** C-A checks the assumptions of stage 2, `EvictRunOK`:
   TREE (`treeFailures`) and A6' (`adoptFailures`, new: the model's
   `adoptAt`) after every transaction, R(0) included, and A-COPY
   (`copyFailures`) for each change; a failure fails the trace. The
   adoptions below the old parent get a line of their own ("C-A adoptions
   below the old parent"). The diagnostics keep D closed upward and INV-2.
   Test traces: `adopt.trace` now fails C-A on TREE, and its adoption is
   below the old parent; a new `adopt2.trace` adopts from outside the old
   parent's subtree and fails A6'; `copy.trace` fails C-A on A-COPY.
3. **The sets.** conformance.sh's small set has a seventh configuration,
   `a6` (as `a6-big` above), and its evict set an eleventh, `e-a6` (as
   `a6-random`); a trace of them without an adoption below the old parent
   fails the set, as a reclaim trace without a cut does. So every run of
   `level2.sh` checks the kind's records (C-S), and every run of `level4.sh`
   its pointers with eviction (C-P); `level3.sh`'s reclaim set gets the
   stage 2 checks through C-A.

Files: `java/stress/A2A3Check2.java`, `level2.sh` and `conformance.sh`;
`lean/Check/Steps.lean`, `lean/TraceCheck.lean`, `lean/README.md` and
`lean/test-traces/` (`run.sh`, `adopt.trace`, the new `adopt2.trace`); and
docs/level2-alignment.md (section 12), level4-alignment.md (M43, section 4),
levels.md and log.md. The tools in [04-a6-failures/](04-a6-failures/) were
written for the checker of `1f4b637`: `traces.sh` reads A6 from the
diagnostics, which no longer have it.

Checks: `lake build` without warnings; `test-traces/run.sh`, TRACE TESTS OK.
The four gates, full, on the clone: `LEVEL 1 OK` (167 s); `LEVEL 2 OK` (752
s: step 7's three configurations with TREE, A6' and A-COPY; the small set's
70 traces `TRACECHECK OK`, every `a6` trace with the kind, 11 transactions
in all); `LEVEL 3 OK` (502 s: 25 reclaim traces, no adoption below the old
parent); `LEVEL 4 OK` (875 s: 33 eviction traces, C-P on 521,711 pointers,
the kind in 3 transactions). Then on the work tree with 005-10's removal, in
a fresh clone, whose `java/` and `lean/` are those of `3fdf88b`: `lake build`
without warnings, TRACE TESTS OK, and the four gates, full: `LEVEL 1 OK` (170
s), `LEVEL 2 OK` (747 s), `LEVEL 3 OK` (469 s), `LEVEL 4 OK` (857 s), with the
same numbers of traces and of adoptions below the old parent.
