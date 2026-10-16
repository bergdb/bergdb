Self-indexed streams in Lean
============================

Started 2026-10-12. Written by Claude for Frans Lundberg.

The model of [../docs/sis-model.md](../docs/sis-model.md) in Lean 4:
the definitions, the assumptions, and the theorems T1 (recovery) and T2
(restart invariance), with their proofs. See Status.

Reviewed 2026-10-13 at the `ebe5f77` documentation cutoff. Lean source is
unchanged from the earlier build, randomized and axiom checks. These are proofs
of the abstract model with the exact still-dirty test, not of Java, reclaim,
eviction, concurrency, serialization, torn bytes or resource bounds.
Java's conservative tracking and reference-resolution obligations are in
[levels.md](../docs/levels.md).


Build and run
=============

Needs elan (`brew install elan-init`). The toolchain version is in
`lean-toolchain`; elan downloads it on first use. No Mathlib.

    cd lean
    lake build              # checks every file, runs the #guard tests
    lake exe sistest 20 40  # random runs: 20 seeds, 40 transactions each (7 min)

`lake build` checks every proof. To see that a theorem depends on nothing but
Lean's standard axioms (no `sorry`), put this in a file, for example
`Axioms.lean`, and run `lake env lean Axioms.lean`:

    import SIS.Theorems
    #print axioms SIS.T1_recovery
    #print axioms SIS.T1_crash
    #print axioms SIS.T1_nodes
    #print axioms SIS.T2_restart
    #print axioms SIS.T13_markExact

Each prints `[propext, Classical.choice, Quot.sound]`.


What to read
============

The trusted part is the definitions and the theorem statements. If they say
what sis-model.md says, a proof that Lean accepts proves the theorems for
the model. Read in this order; each definition has a comment that points to
its section in sis-model.md.

| File | Contents | sis-model.md |
|---|---|---|
| SIS/Basic.lean | Entries, histories, x@t (`upTo`), nodes, P (`Struct`), changes, the structure's functions (`Spec`, with the virtual root's switch `virt`, `topLevel` and `rootVal`), root children (`isTop`), reachability, P@t (`view`), equivalence (`Equiv`) | 2, 3 |
| SIS/Stream.lean | Versions, records (top(i) as a node and a record), the stream, lv(x) (`Stream.lv`), references, `good`, `dirty` | 4, 5 |
| SIS/Algorithm.lean | DB = <P, D, S>, the policy, the still-dirty test and the choice of step 3 (`Algo`), the exact and BergDB's still-dirty tests (`exactTest`, `javaTest`), marking (`changed`, `marked`, `markOf`), what can be in D and written (`written`), top(i) (`topOf`, `topV`), transaction i (`step`), R(0) (`init`), `run` | 6.1 |
| SIS/Startup.lean | `newest` (R(s) to R(k)), Rule R (`follow`), reading the stream (`readFrom`), where reading starts (`topVersion`, `startVersion`; with a virtual root `readTops`, `topsRead`, `rootVersion`), P up to s (`baseStruct`), `rerun`, `startup` | 6.2 |
| SIS/Assumptions.lean | Assumptions A2 to A5 and the data node rules (`SpecOK`, `StepOK`, `RunOK`), with a virtual root R1 to R4 (`VirtInit`, `VirtStep`, `topClosure`), `runRestarts` | 3.4 |
| SIS/Theorems.lean | T1 (`T1_recovery`, `T1_crash`, `T1_nodes`), T2 (`T2_restart`), T13 (`T13_markExact`) | 9 |

The proofs, in SIS/Proof/ (not needed for reading the statements):

| File | Contents |
|---|---|
| Basic, Reach | Histories, nodes, reachability as an inductive definition, growing structures |
| StreamLemmas, Write | Latest versions, `good` and `dirty`, stability (`good_mono`), writing versions |
| Run | The parts of a transaction, runs, and the invariant `Inv` (INV-1 to INV-4 and the facts about S and P) |
| Init, Util, StepFacts, StepP, StepS, StepD, StepInv | The invariant holds after T(0) and after every transaction (`inv_st`) |
| Mark | Marking the access path of the change finds exactly the dirty index nodes not in D (`step_marked_iff`, T13) |
| Still | What the proofs need of the still-dirty test (`StillOK`), for the exact test and BergDB's (`java_stillOK`) |
| VStep | With a virtual root, the transaction keeps `VInv` (`step_vinv`): the root children, the root's history, R4, and that the latest version of a root child names the latest versions of the root children it points to (`step_fresh`, which needs BergDB's still-dirty test) |
| RunFacts | How the states of a run relate |
| Recon | L-OUT (`Inv.lout`) and L-SEC (`Inv.recon`), reading with Rule R |
| Read | Reading from a version that is good with Rule R (`Inv.read`) |
| VRead | With a virtual root, startup reads every root child created up to s, at its latest version, and rebuilds the root (`Inv.readAt_spec_virt`) |
| Base | Reading the stream (`Inv.readAt_spec`), P up to s (`Inv.base_get?`) |
| Recovery | The rerun, and T1 in the strong form (`T1_strong`) |
| Restart | Every part of a transaction depends on P only through its nodes, and T2 (`T2_strong`) |

Not trusted, tests only:

* SIS/Example.lean. The example of section 7, checked with `#guard`; a
  second structure with four levels, data nodes and time splits; and a third
  with a virtual root, as in BergDB: top nodes with a dead pointer to the
  previous one, and root splits that make a new top node. Also a check by
  running that a run meets the assumptions (`runOKB`, with `virtStepB` for
  R1 to R4).
* Test.lean. Runs the second structure on pseudo-random transactions and
  checks the assumptions, T1 in every state, and T2 with random restarts,
  for 16 algorithms (4 policies, the exact and BergDB's still-dirty test,
  step 3 by testing or by marking), and that marking gives the same records
  as testing; then the third structure for 8 algorithms (4 policies, step 3
  by testing or by marking, BergDB's test); and it reports how often the
  exact test fails T1 with the virtual root, which the theorems do not
  cover.
* Check/ and TraceCheck.lean: the trace checker, `lake exe tracecheck`. It
  checks traces of Java runs against the model's definitions
  ([../docs/level2-alignment.md](../docs/level2-alignment.md), sections 8.5
  and 9). `sh test-traces/run.sh` runs its tests.

Choices made in Lean that the text leaves open:

* Node ids and times are natural numbers; root has id 0.
* A reference is the record number of the version (a node is written at
  most once per record), and a missing reference is a vpos.
* `good` and the reading of the stream do not follow a pointer to a node
  that is not on a lower level. This makes the recursion end, and changes
  nothing for a structure that has A4.
* gd(i) lists the nodes of step 3 sorted by id, then those of step 7, so
  that a record does not depend on the order of nodes in P.
* Step 7 tests the taken nodes lowest level first, adding each still-dirty
  node to D before the next test, so that the conservative test sees
  children that stayed dirty.
* P after startup is a list of nodes: each node reached when reading the
  stream at some time t <= s, with the history of the version it is read
  from at the latest such t, cut at s; then the rerun.
* Step 3 lists the nodes of P by id (`allIds`), sorted, so that a record
  does not depend on the order of the nodes in the list that holds P.
* `Time` and `NodeId` are notations for `Nat`, so that arithmetic
  automation (`omega`) sees through them.
* T1 and T2 are stated for the exact still-dirty test and for BergDB's
  conservative one (`javaTest`), since 2026-10-15; with a virtual root, for
  BergDB's only (since 2026-10-16).
* With a virtual root, top(i) is the root's child named by the root's last
  entry up to s(i), with the record of its latest version (`topV`). BergDB's
  topPos names the latest version of the newest top node written; the trace
  checker compares the two (C-S).
* With a virtual root, startup rebuilds the root's history from the root
  children read: for each time t <= s, the entry (t, rootVal z) of the root
  child z whose entries are at t (`rootVersion`).


Reading Lean
============

Enough to read the trusted part:

* `def f (x : A) : B := ...` defines a function f from A to B. Arguments in
  `{ }` are filled in by Lean; `[DecidableEq V]` says that values of type V
  can be compared.
* `structure` is a record type with named fields; `{ f := 1, g := 2 }`
  builds one, `r.f` reads a field, `{ r with f := 3 }` copies with a change.
* `Option A` is `some a` or `none`. `List A` is a list; `xs.map f`,
  `xs.filter p`, `xs.foldl f a` (a loop), `xs.flatMap f`, `xs.all p`,
  `xs.any p` are the usual list functions. `List.range n` is 0, ..., n-1.
* `match e with | p => ...` is a case analysis. `fun x => e` is a lambda.
* `termination_by n.level` tells Lean why a recursive definition ends: the
  level goes down at each call.
* `Prop` is the type of statements; `∀`, `∃`, `∧`, `∨`, `→` are as in logic.
  A `theorem` is a statement followed by its proof after `:= by`.
* `Bool` values are `true` and `false`; `b = true` turns one into a
  statement.

Two good introductions, if more is wanted: Functional Programming in Lean
(chapters 1 and 2) and Theorem Proving in Lean 4.


Status
======

2026-10-12. Milestone 1: the definitions, the assumptions, T1 and T2
stated, the examples. The first random runs found a gap in sis-model.md:
Rule R must also follow vpos pointers. Fixed.

2026-10-12. Milestones 2 to 5: T1 and T2 proven, in the strong forms
`T1_strong` (startup gives back every node, with its whole history, and D)
and `T2_strong` (a run with restarts stays in step with the run without).
`lake build` passes with no warnings and no `sorry`; `#print axioms` shows
only Lean's standard axioms. `lake exe sistest 20 40` passes.

2026-10-13. Fresh documentation-review checks: `lake build` passed all
27 jobs; `lake exe sistest 20 40` reported assumptions, T1 and T2 passing
20/20 seeds for each of eight algorithm variants. A fresh `#print axioms`
check of T1_recovery, T1_crash, T1_nodes and T2_restart printed only
`[propext, Classical.choice, Quot.sound]`. This reconfirms the existing
proofs; no new theorem or Java validation is implied. `good_mono` is
stability of a fixed version as the logical structure grows, not the
unproved Java lemma M about substituting a newer version.

2026-10-15. Marking (WP E1 of F1-008-11, repository f1): A5 added to the
assumptions, step 3 by marking (`Algo.mark`), T13 proven, and T1 and T2 for
both ways of step 3. `lake build` passes with no warnings and no `sorry`;
`lake exe sistest 20 40` passes for 16 algorithms, and marking gives the same
records as testing for 20/20 seeds; `#print axioms` of T1, T2 and
`T13_markExact` shows only Lean's standard axioms. Also new: the trace
checker (Check/, TraceCheck.lean), not part of the trusted part.

2026-10-15. BergDB's still-dirty test (WP E2 of F1-008-11): `javaTest`, Rule
A over all pointers, as in bergdb's `DbHelper.hasDirtyChild`. T1, T2 and T13
now hold for both still-dirty tests, the exact one and BergDB's
(`Proof/Still.lean`: the proofs need only that the test looks at P through
its nodes and puts back every written node that is still dirty; BergDB's
test does, because step 7 tests the written nodes lowest level first).
Together with marking, the model's bookkeeping is now BergDB's. `lake build`
passes with no warnings and no `sorry`; `#print axioms` as above.

2026-10-16. The remaining Level 2 model changes (WP E3 of F1-008-11): the
virtual root of option (a), Rule R from R(s) on (M7), and a policy that sees
the transaction (M10). T1, T2 and T13 hold with and without a virtual root.
`lake build` passes with no warnings and no `sorry`; `#print axioms` as above;
`lake exe sistest 20 40` passes for the 16 algorithms of the second structure
and the 8 of the third (the virtual root). The trace checker now runs the
model's own `init` and `step`, with no checker-local definitions, and checks
R1 to R4 (C-A).

2026-10-16. The conformance campaign (WP F1 of F1-008-11): on bergdb
`d5c56dd`, the checker found every transaction of 59 traces of Java runs (50
small, 9 medium) a step of the model in the target mode, with no change to
the model (../docs/level2-alignment.md, 10.5).

Changes to the trusted part while proving, all on 2026-10-12:

* A2 (`StepOK.current`): entries only to nodes reachable at time i after
  the change, instead of reachable at time i-1 or new. Without it, a
  transaction could add an entry to a node and cut it off in the same step;
  startup could not rebuild that entry. See sis-model.md, section 14.
* A3: `noResurrection` removed; the proofs do not need it.
* `step` split into named parts (`gotDirtyOf`, `startupPos`,
  `stillDirtyOf`), and step 3 lists nodes through `allIds` and `isIndex`.
  The same algorithm, written so that it does not depend on the order of
  nodes in P.
* The assumptions moved from Theorems.lean to Assumptions.lean.
* `T1_crash` added: T1 stated for a crash after any T(k), from the first
  k+1 records of a longer run's stream.
* `T1_nodes` added: the stronger form of T1.

Changes to the trusted part on 2026-10-15 (F1-008-11, WP E1;
[../docs/level2-alignment.md](../docs/level2-alignment.md), M2):

* A5, no resurrection (`StepOK.noRes`): a node reachable after a transaction
  was reachable before it, or is new. Added because marking needs it: a node
  that becomes reachable again with nothing changed below it could be dirty
  without being on the access path of the change. BergDB meets it (the trace
  checker found no failure).
* Step 3 may mark the access path of the change instead of testing every
  index node (`Algo.mark`, default false; `changed`, `marked`, `markOf`):
  BergDB's way. T13 (`T13_markExact`): for an index node not in D, marked is
  the same as dirty, so both ways give the same records, and T1 and T2 hold
  for both (their proofs use T13 when `al.mark` is true).
* BergDB's still-dirty test, `javaTest` (WP E2): a written node goes back
  into D if one of its pointees, live or dead, is in D. The hypothesis of T1,
  T2 and T13 changed from `al.stillDirty = exactTest sp` to
  `al.stillDirty = exactTest sp ∨ al.stillDirty = javaTest sp`: the theorems
  now cover both tests.

Changes to the trusted part on 2026-10-16 (F1-008-11, WP E3;
[../docs/level2-alignment.md](../docs/level2-alignment.md), M7, M10, M11 and
section 8):

* M7: `newest`, and so Rule R, looks at R(s), ..., R(k), as BergDB's
  `DbStarter.createMaps` does, instead of R(s+1), ..., R(k). The proofs needed
  only `<` changed to `≤` in L-SEC.
* M10: the startup pos policy also gets the transaction T(i)
  (`Algo.policy`, `startupPos`), as BergDB's `TransSeq.take` depends on the
  transaction's size.
* M11, option (a) of Q7, the virtual root. `Spec` gets `virt` (default
  false: the root is an ordinary node, as before), `topLevel` and `rootVal`.
  With `virt`: step 3 never gives the root (`written`), R(0) does not write it,
  and top(i) names the root's child at s(i) and the record of its latest
  version (`topOf`, `topV`); `Record.top` is now a node and a record. Startup
  reads the root children from that version through their pointers, live or
  dead (`readTops`, with Rule R), and rebuilds the root (`rootVersion`), then
  reads as before (`startVersion`).
* With a virtual root, new assumptions (`VirtInit`, `VirtStep`): R1, the
  root's entry for child z points to z; at most one initial root child and at
  most one new root child per transaction, an index node with entries; R3, a
  root child gets entries only in the transaction that creates it; R2, the
  root gets exactly the entry for the new root child; R4, every older root
  child can be reached from the new one through pointers between root
  children; and a root child that a root child points to is not reachable.
  BergDB meets them (the trace checker checks them, C-A).
* The hypothesis of T1, T2 and T13: BergDB's still-dirty test, or, without a
  virtual root, the exact one. With a virtual root the proofs need BergDB's
  test: it puts a written top node back into D when an older top node it
  points to is in D, so the latest version of a top node that stayed clean
  names the latest versions of the older top nodes it points to
  (`VInv.fresh`), and startup, which finds older top nodes only through these
  references, reads them right. With the exact test a top node can keep a
  reference to a stale version of an older top node: `exactWitness3` in
  SIS/Example.lean is a run where T1 then fails.
* T13's statement says "an index node other than a virtual root"
  (`written`).

Not done:

* Lazy reading after a restart, as BergDB reads a node on first touch (lemma
  M of ../docs/levels.md; M8 of ../docs/level2-alignment.md): the model
  reads all of P up to s at startup.
* The bounds (T3, T4), eviction, reclaim.
