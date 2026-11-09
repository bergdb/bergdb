020-29-index-proof
==================

Created 2026-11-09 by Frans Lundberg. Status: open.

A Lean proof, for every size, of the safety invariants of 2026.4's user
indexes that 020-26 checked with TLC within small bounds: the protocol of
020-10 with 020-18's F1, F3, F4 and F5, as 020-26's IndexModel.tla states
it, in Lean, and its invariants proved by induction over the steps.


Files
=====

On the branch `020-29-index-proof`, in `lean/` (the library `BergDB`, beside
`SIS`; `lake build BergDB` builds it alone, and `lake build` builds it too):

* `lean/BergDB/Index/Model.lean`. The trusted part: the protocol (section 2).
* `lean/BergDB/Index/Theorems.lean`. The theorems' statements (section 3).
* `lean/BergDB/Index/Inv.lean`. The invariant, its frames (section 4).
* `lean/BergDB/Index/Steps.lean`. A lemma per kind of step, the induction.
* `lean/BergDB/Index/Example.lean`. A run of the model (section 5).
* `lean/BergDB.lean`, `lean/lakefile.toml`. The library's root, its entry.


## 1. The request

From coord-1109 (2026-11-09, 17:27, at Frans's word of 17:26): a Lean proof,
for all sizes, of the main invariants of 2026.4's user-index protocol, which
020-26 checked with TLA+ and TLC only for small bounds. In order, stopping at
what can be finished well: (a) the abstract protocol in Lean; (b) the main
safety invariant, at every lookup time an active index's entries equal f over
the data and no stale entry is visible; (c) its proof by induction over the
steps, after 020-26's nine points; (d) the building phase's invariant. In a
clone, on a branch, nothing in 2026.4; no Mathlib.

All four are done, with no `sorry` and no axiom of its own (section 6).


## 2. The model

020-26's IndexModel.tla, step for step (its section 2.3), in Lean 4.34.1
without Mathlib: one index name over one directory; transactions of one key.

* **The stream** (`Stream`), what a crash keeps: the data (key to value),
  the definition (G, its function, building or active), the entries (a set
  of (G, key, levels)), the markers, the latest time, and the time of the
  last write of each key, of the definition's key and of the directory's
  virtual key. The last write times are the Core's conflict check as
  `Db.stmCheckConflicts` makes it: a transaction with read time R is refused
  if a key of its read set was written after R. With them the model needs no
  `ws` per transaction, as the TLA+ model has, and no history.
* **Memory** (`Mem`), lost at a crash: the manager's lock (free, a definition
  change, or a build's locked phase), its maps, a definition change between
  its commit and its maps, the writers' transactions, the builds and the
  cleanups by generation.
* **The past**: the streams of the earlier times, newest first. A lookup at
  time t reads the stream of t (`Sys.at`). A crash may go back to any of
  them: the crash contract allows losing the last committed transactions
  (levels.md, section 8), which 020-26 argued in words and here is a step.
* **What is a parameter**: the values, the index functions and the levels are
  any types; f is any function of the key and the value with zero or one
  entry per value, none for no value and none at a key with a suffix (020-10,
  section 3.3); `lockedAfter`, the tries before the locked phase, any number.
* **The steps** (`Step`): `wSuffix`, `wStart`, `wReadS`, `wCommit`, `wDrop`;
  `aCreate`, `aCreateMap`, `aDelete`, `aDeleteMap`; `bReadE`, `bRead`,
  `bCheck`, `bCheckFail`, `bCommit`, `bRefused`, `bLock`, `bActivate`,
  `bActivateFail`; `cScan`, `cScanEnd`, `cDel`, `cEnd`; `crash`, which
  restarts as `IndexManager.start` does. Each is TLA+'s action of the same
  name; their comments cite 020-10.
* **Where the model allows more than the code**, so that the theorems hold
  for the code's choices too: a build step reads any range of keys up to E
  (the code: 25 values or 1 MB); E is any key after which the directory has
  no value (the code: its last key); a cleanup's scan deletes any set (the
  code: 100 entries after the last deleted); a transaction in flight may end
  without a commit at any time (`wDrop`: refused, then run again as a new
  transaction, or an exception); a crash may lose committed transactions.
* **Left out**, as in 020-26, section 2.4: several names, several directories
  and transactions of several keys; writes through the Core, key replace,
  reclaim's cut of lookup times, format 1. And liveness (section 7).

`G` is the latest transaction's time when the creation runs, as in the code
and 020-26's `TimedGen`.


## 3. The theorems

For every reachable system (`Reach`: from a database with any data and no
index, any sequence of steps), with nothing but Lean's standard axioms:

* `index_is_function` (020-26's IndexIsFunction): at every lookup time, an
  active index's entries are exactly f over the directory's values.
* `no_stale_entry` (NoStaleEntry): at every lookup time, also while the index
  builds, no entry of the live generation is stale.
* `build_covers` (BuildCovers): the keys a build has passed, and those after
  its end key E, have exactly their entry.
* `gens_accounted` (GensAccounted): a generation with entries is the live
  one or has a marker.
* `start_accepted` (MarkerNotLive, StartAccepted): no marker names the live
  generation, so no start refuses the database.
* `gen_fresh` (GenFresh): the G a creation takes is in no definition,
  marker, entry, build or cleanup.
* `mem_agrees` (MemAgrees): with no definition change under way, the maps are
  the stream's definition.
* `lock_sane` (LockSane): the lock is held by a definition change exactly
  while one is under way, and by a build exactly in its locked phase.
* `cleanup_done_empty` (020-26, section 4, point 6): a cleanup at its end
  leaves no entry of its generation.
* `writer_sees_live` (points 1 and 2): a writer's transaction that the Core
  will accept read the live index set.

The main one, in Lean:

```lean
theorem index_is_function {sp : Spec V F L} {s : Sys V F L W} (h : Reach sp s) {t : Time}
    {x : Stream V F L} (hx : s.at t = some x) {d : Def F} (hd : x.dfn = some d)
    (ha : d.active = true) (k : Key) (l : L) :
    x.ent d.gen k l ↔ sp.f d.fn k (x.data k) = some l
```

020-26's invariants are all here, and in the strong form that its runs
checked: the raw entries, not a scan's view (a scan, which skips a stale
entry, can only see less).


## 4. The proof

An inductive invariant `Inv` (Inv.lean), kept by every step (`inv_step`,
Steps.lean), so held by every reachable system (`reach_inv`). It has three
parts:

* `SInv`, of the stream alone: every generation and marker before the
  latest time; NoStaleEntry; every key covered while the index is active;
  GensAccounted; MarkerNotLive. Being of the stream alone, it holds of every
  stream a crash goes back to, and a start makes memory's part anew from it
  (`minv_restart`).
* `MInv`, of memory with the stream: MemAgrees, the lock, the definition
  change in progress, and an invariant per thread: `WInv` per writer,
  `BInv` per build (with `StepInv` for a step between its read and its
  commit), `CInv` per cleanup.
* `SInv` of every earlier stream: the lookups at earlier times.

020-26, section 4's points, where they are:

1. A writer that commits in G's life keeps G: `WInv` (if the virtual key was
   not written after R, the index set read is the live one; if the key was
   not written after R, the previous value read is the key's value) and
   `step_wCommit` (the key's entries become exactly f(new)).
2. No writer writes G after its deletion: the same `WInv`; the deletion
   writes the virtual key (`step_aDelete`).
3. A build step commits only in G's life, with exact entries: `BInv.live`
   (if the definition's key was not written after R, G is live: `isLive` held
   after R, `minv_bCheck`) and `StepInv.snap` (a value whose entry the step
   puts is its key's value), `step_bCommit`.
4. Coverage: `BInv.cover` with `StepInv.noneCov` (a key whose value had no
   entry at R is covered, as every writer since kept it) and `minv_bReadE`
   (the keys after E have no value).
5. The activation: `BInv.done` (every key passed), `step_bActivate`.
6. No orphans: `SInv.accounted`, `CInv` (a cleanup at its end leaves no entry
   of its generation, and no step puts one), `step_cEnd`.
7. Fresh generations: `SInv.gen_lt`, `SInv.mark_lt`, `MInv.bLt`: everything
   is before the latest time, which a creation takes as G (`step_aCreate`).
8. and 9. Builds and cleanups end: liveness, not proved here (section 7).

The step lemmas that commit a transaction are stated over any stream with the
fields the step gives, so that their proofs rewrite with them; the frame
lemmas (`WInv.frame`, `BInv.frame`, `MInv.frameS`) say what a commit keeps of
the threads in flight: a commit writes its keys at the time now + 1, after
every R, so a transaction with one of them in its read set will be refused,
and the other keys keep their values.


## 5. The run

`example_run` (Example.lean) checks that the model is not empty: a database
with the value 7 at key 0 creates an index, builds it in one step, activates
it; a writer puts 9 at key 0; the index then has the entry 9 and, by
`index_is_function` applied to that run, not the entry 7. Each step's
conditions are met by computation (`rfl`, `decide`).


## 6. How to check

In the clone (`/Users/f/fl/bench/2026-11-09/clone-l29`), or wherever the
branch is checked out:

    cd lean
    lake build BergDB           # about 10 s from clean, the library alone

and the axioms, from a file outside the library with
`lake env lean Axioms.lean`:

    import BergDB.Index.Theorems
    #print axioms BergDB.Index.reach_inv
    #print axioms BergDB.Index.index_is_function
    #print axioms BergDB.Index.no_stale_entry
    #print axioms BergDB.Index.build_covers
    #print axioms BergDB.Index.gens_accounted
    #print axioms BergDB.Index.start_accepted
    #print axioms BergDB.Index.gen_fresh
    #print axioms BergDB.Index.mem_agrees
    #print axioms BergDB.Index.lock_sane
    #print axioms BergDB.Index.cleanup_done_empty
    #print axioms BergDB.Index.writer_sees_live

Each prints `[propext, Classical.choice, Quot.sound]` (2026-11-09).
`grep -rn sorry lean/BergDB` finds none.


## 7. State

**Proved**, for any number of keys, writers, build steps of any size,
generations, deletions, creations again and crashes (also crashes that lose
committed transactions): every invariant of 020-26, section 3 (section 3
above), with no `sorry`. So 020-26's safety results hold beyond its bounds:
no design fault, for every size, in the protocol as 020-26 models it.

**Not proved**:

* **Liveness**: 020-26's BuildEnds, CleanupEnds and NoOrphans (its points 8
  and 9), under fairness. They need a model of fairness (weak fairness of a
  thread's steps, writers that may write for ever) and a ranking argument:
  the keys up to E are finitely many; a step in the locked phase can be
  refused only by writers that read S before the lock was taken, each at
  most once. A Lean statement could be: in every fair infinite run, the
  definition leaves `building`. Not started.
* **The extensions 020-26 left out**: several names (each with its own
  definition, generations, markers and entries; one lock; the virtual key per
  directory), several directories, and transactions of several keys (one
  read time, a key's read set per indexed key, the virtual keys of each
  directory). The proof's structure carries over: the invariant per name and
  per key. Not started.
* **The Java code**: the theorems are about the model; the model follows
  020-26's, which follows the code at `83e8e13` with 020-18's fixes. When the
  code changes the read sets, the lock or the order of R and S, the model
  must follow (020-26, section 8).

**How to continue**: liveness first (it is what TLC could check only within
bounds and with few writers); then several names, by making the stream's
definition, entries and markers functions of the name and the lock's maps
per name, with the same lemmas per name.


Log
===

2026-11-09. Created by coord-1109's agent l29 (17:27), at Frans's word
(17:26): the model, the invariant and its proof, the theorems and the run,
in a clone at `/Users/f/fl/bench/2026-11-09/clone-l29`, branch
`020-29-index-proof`. `lake build BergDB` clean, no `sorry`, the standard
axioms only. Nothing in 2026.4. For the coordinator: a line for this
subitem in 020's readme, Files.
