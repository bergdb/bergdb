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
    lake exe sistest 20 40  # random runs: 20 seeds, 40 transactions each

`lake build` checks every proof. To see that a theorem depends on nothing but
Lean's standard axioms (no `sorry`), put this in a file, for example
`Axioms.lean`, and run `lake env lean Axioms.lean`:

    import SIS.Theorems
    #print axioms SIS.T1_recovery
    #print axioms SIS.T1_crash
    #print axioms SIS.T1_nodes
    #print axioms SIS.T2_restart

Each prints `[propext, Classical.choice, Quot.sound]`.


What to read
============

The trusted part is the definitions and the theorem statements. If they say
what sis-model.md says, a proof that Lean accepts proves the theorems for
the model. Read in this order; each definition has a comment that points to
its section in sis-model.md.

| File | Contents | sis-model.md |
|---|---|---|
| SIS/Basic.lean | Entries, histories, x@t (`upTo`), nodes, P (`Struct`), changes, the structure's four functions (`Spec`), reachability, P@t (`view`), equivalence (`Equiv`) | 2, 3 |
| SIS/Stream.lean | Versions, records, the stream, lv(x) (`Stream.lv`), references, `good`, `dirty` | 4, 5 |
| SIS/Algorithm.lean | DB = <P, D, S>, the policy and the still-dirty test (`Algo`), transaction i (`step`), R(0) (`init`), `run` | 6.1 |
| SIS/Startup.lean | `newest`, Rule R (`follow`), reading the stream (`readFrom`), P up to s (`baseStruct`), `rerun`, `startup` | 6.2 |
| SIS/Assumptions.lean | Assumptions A2 to A4 and the data node rules (`SpecOK`, `StepOK`, `RunOK`), `runRestarts` | 3.4 |
| SIS/Theorems.lean | T1 (`T1_recovery`, `T1_crash`, `T1_nodes`) and T2 (`T2_restart`) | 9 |

The proofs, in SIS/Proof/ (not needed for reading the statements):

| File | Contents |
|---|---|
| Basic, Reach | Histories, nodes, reachability as an inductive definition, growing structures |
| StreamLemmas, Write | Latest versions, `good` and `dirty`, stability (`good_mono`), writing versions |
| Run | The parts of a transaction, runs, and the invariant `Inv` (INV-1 to INV-4 and the facts about S and P) |
| Init, Util, StepFacts, StepP, StepS, StepD, StepInv | The invariant holds after T(0) and after every transaction (`inv_st`) |
| RunFacts | How the states of a run relate |
| Recon | L-OUT (`Inv.lout`) and L-SEC (`Inv.recon`), reading with Rule R |
| Base | Reading the stream (`Inv.readAt_spec`), P up to s (`Inv.base_get?`) |
| Recovery | The rerun, and T1 in the strong form (`T1_strong`) |
| Restart | Every part of a transaction depends on P only through its nodes, and T2 (`T2_strong`) |

Not trusted, tests only:

* SIS/Example.lean. The example of section 7, checked with `#guard`, and a
  second structure with four levels, data nodes and time splits. Also a
  check by running that a run meets the assumptions (`runOKB`).
* Test.lean. Runs the second structure on pseudo-random transactions and
  checks the assumptions, T1 in every state, and T2 with random restarts.

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
* T1 and T2 are stated for the exact still-dirty test. The conservative
  test is checked by the random runs only.


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

Not done:

* T1 and T2 for the conservative still-dirty test, or any sound test.
* The bounds (T3, T4), eviction, reclaim.
