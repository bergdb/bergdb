020-29-index-proof
==================

Created 2026-11-09 by Frans Lundberg. Status: open.

A Lean proof, for every size, of the safety invariants of 2026.4's user
indexes that 020-26 checked with TLC within small bounds: the protocol of
020-10 with 020-18's F1, F3, F4 and F5, as 020-26's IndexModel.tla states it
and more (several index names and directories, transactions of any keys), in
Lean, and its invariants proved by induction over the steps.


Files
=====

On the branch `020-29-index-proof`, in `lean/` (the library `BergDB`, beside
`SIS`, which it does not import; `lake build BergDB` builds it alone, and
`lake build` builds it too):

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

All four are done, with no `sorry` and no axiom of its own (section 6), and
for more than 020-26's model: any number of index names and directories, and
transactions that write any keys (section 2).


## 2. The model

020-26's IndexModel.tla, action for action (its section 2.3), in Lean 4.34.1
without Mathlib, with what its section 2.4 left out of the writers and the
names: several index names, each a definition over a directory; several
directories, each with its virtual key; transactions that write any keys, in
any directories, each with its new value or a delete (the last call on a key
wins, 015-41).

* **The stream** (`Stream`), what a crash keeps: the data (key to value);
  per name, the definition (G, its function with its directory, building or
  active), the entries (a set of (G, key, levels)) and the markers; the
  latest time; and the time of the last write of each key, of each name's
  definition key and of each directory's virtual key. The last write times
  are the Core's conflict check as `Db.stmCheckConflicts` makes it: a
  transaction with read time R is refused if a key of its read set was
  written after R. With them the model needs no `ws` per transaction, as the
  TLA+ model has, and no history.
* **Memory** (`Mem`), lost at a crash: the manager's lock (free, a definition
  change, or a build's locked phase), its maps (name to definition), a
  definition change between its commit and its maps, the writers'
  transactions, the builds and the cleanups by name and generation.
* **The past**: the streams of the earlier times, newest first. A lookup at
  time t reads the stream of t (`Sys.at`). A crash may go back to any of
  them: the crash contract allows losing the last committed transactions
  (levels.md, section 8), which 020-26 argued in words and here is a step.
* **What is a parameter**: the values, the index functions and the levels are
  any types; f is any function of the key and the value with zero or one
  entry per value, none for no value, none at a key with a suffix and none at
  a key of another directory than its index's (020-10, section 3.3);
  `lockedAfter`, the tries before the locked phase, any number.
* **Writers** (`WSt`), as `RwEnvironmentImp.indexEntries` does it: a
  transaction fixes R and reads the previous values at R (`wStart`); it reads
  the index set of each key's directory under the lock, a key at a time
  (`wReadS`, `IndexManager.getActiveIndexesForDir`: each read takes the lock
  anew, so a definition change can come between two of them); it commits
  (`wCommit`) if no key of its read set was written after R: the virtual key
  of each written object key's directory, and each written object key whose
  set has an index of its directory (a key with a suffix adds nothing, as
  `objectOps` has object keys only). At each key written, for each index of
  its set, f(old) is deleted and f(new) put. A `w()` of keys with a suffix
  only has no R and no read set (`wSuffix`). An `rw()`'s own reads only add keys to its
  read set, so more refusals, which `wDrop` allows.
* **The other steps** (`Step`): `aCreate`, `aCreateMap`, `aDelete`,
  `aDeleteMap` (a definition change of a name: under the lock, its commit
  writes the definition's key and the virtual key of the index's directory,
  then the maps); `bReadE`, `bRead`, `bCheck`, `bCheckFail`, `bCommit`,
  `bRefused`, `bLock`, `bActivate`, `bActivateFail` (a build); `cScan`,
  `cScanEnd`, `cDel`, `cEnd` (a cleanup); `crash`, which restarts as
  `IndexManager.start` does. Each is TLA+'s action of the same name; their
  comments cite 020-10. Three more, of the code's errors (020-10, 6.1 and
  6.2, "Errors"), which 020-26 left out: `bRetry`, a step's try ended by an
  exception that the build takes again (`DbException`, an expired read), the
  step again from its start, unlocked (`underLock` released the lock);
  `bAbort`, a build's thread that ends without its activation (FAILED, or a
  stop), its lock released; `cAbort`, a cleanup's thread that ends, its
  marker kept for the next start. And `cut`, reclaim's cut of lookup times:
  the oldest streams gone from the past (a lookup or a transaction at a time
  cut is refused, which `wDrop` and `bRetry` allow).
* **Where the model allows more than the code**, so that the theorems hold
  for the code's choices too: a build step reads any range of keys up to E
  (the code: 25 values or 1 MB); E is any key after which no value has an
  entry (the code: the directory's last key); a cleanup's scan deletes any
  set (the code: 100 entries after the last deleted); a writer may read the
  index set of any key, and a transaction in flight may end without a commit
  at any time (`wDrop`: refused, then run again as a new transaction, or an
  exception); a crash may lose committed transactions.
* **Left out**, as in 020-26, section 2.4: writes through the Core (020-22:
  undefined) and key replace (`${transactionTime}`, 020-10, section 5.3). And
  liveness (section 7). Format 1 is in as f with no entry for a value of
  format 1, as the code takes a previous value of format 1; a put of one is
  refused (`wDrop`) and a build over one fails (`bAbort`).

`G` is the latest transaction's time when the creation runs, and at least 1,
as in the code (`Math.max(1, db.lookupTime(Long.MAX_VALUE))`); 020-26's
`TimedGen` takes the time. With one name, one directory, transactions of one
key and none of the three error steps, the model is 020-26's.


## 3. The theorems

For every reachable system (`Reach`: from a database with any data and no
index, any sequence of steps), for every index name, with nothing but Lean's
standard axioms:

* `index_is_function` (020-26's IndexIsFunction): at every lookup time, an
  active index's entries are exactly f over the data.
* `no_stale_entry` (NoStaleEntry): at every lookup time, also while the index
  builds, no entry of its live generation is stale.
* `build_covers` (BuildCovers): the keys a build has passed, and those after
  its end key E, have exactly their entry.
* `gens_accounted` (GensAccounted): a generation with entries is its name's
  live one or has a marker.
* `start_accepted` (MarkerNotLive, StartAccepted): no marker names a live
  generation, so no start refuses the database.
* `gen_fresh` (GenFresh): the G a creation takes is in no definition,
  marker, entry, build or cleanup of its name.
* `mem_agrees` (MemAgrees): with no definition change under way, the maps are
  the stream's definitions.
* `lock_sane` (LockSane): the lock is held by a definition change exactly
  while one is under way, and by a build exactly in its locked phase.
* `cleanup_done_empty` (020-26, section 4, point 6): a cleanup at its end
  leaves no entry of its generation.
* `writer_sees_live` (points 1 and 2): the index set a writer read for a key,
  if the Core will accept it on the key's virtual key, agrees with the
  definitions for the key's directory.

The main one, in Lean:

```lean
theorem index_is_function {sp : Spec V F L} {s : Sys V F L W} (h : Reach sp s) {t : Time}
    {x : Stream V F L} (hx : s.at t = some x) {n : Name} {d : Def F} (hd : x.dfn n = some d)
    (ha : d.active = true) (k : Key) (l : L) :
    x.ent n d.gen k l ↔ sp.f d.fn k (x.data k) = some l
```

020-26's invariants are all here, and in the strong form that its runs
checked: the raw entries, not a scan's view (a scan, which skips a stale
entry, can only see less).


## 4. The proof

An inductive invariant `Inv` (Inv.lean), kept by every step (`inv_step`,
Steps.lean), so held by every reachable system (`reach_inv`). It has three
parts:

* `SInv`, of the stream alone, for each name: every generation and marker
  before the latest time; NoStaleEntry; every key covered while the index is
  active; GensAccounted; MarkerNotLive. Being of the stream alone, it holds of
  every stream a crash goes back to, and a start makes memory's part anew
  from it (`minv_restart`).
* `MInv`, of memory with the stream: MemAgrees (per name, but for the name of
  a change under way), the lock, the definition change in progress, and an
  invariant per thread: `WInv` per writer, `BInv` per build (with `StepInv`
  for a step between its read and its commit), `CInv` per cleanup.
* `SInv` of every earlier stream: the lookups at earlier times.

The names share the data, the time, the lock and the virtual keys of their
directories. What ties a writer's index set to the definitions is `sameOn`:
for the directory of the key the set was read for, the set and the
definitions name the same indexes (generation and function), in whatever
state. Every change of a name's definition that matters to a directory writes
that directory's virtual key: a creation the new index's, a deletion the old
one's (also when a name is created again over another directory); an
activation changes no generation or function.

020-26, section 4's points, where they are:

1. A writer that commits in G's life keeps G: `WInv` (if the virtual key of a
   key's directory was not written after R, the set read for the key agrees
   with the definitions for that directory; if the key was not written after
   R, the previous value read is the key's value) and `wcommit_exact` (at
   each key written, each live index's entries become exactly f(new); for an
   index of another directory, f has none and the set read gives none).
2. No writer writes G after its deletion: `wcommit_live` (a writer puts an
   entry only for an index of the set it read that is live); the deletion
   writes the virtual key (`step_aDelete`).
3. A build step commits only in G's life, with exact entries: `BInv.live`
   (if the definition's key was not written after R, G is live: `isLive` held
   after R, `minv_bCheck`) and `StepInv.snap` (a value whose entry the step
   puts is its key's value), `step_bCommit`.
4. Coverage: `BInv.cover` with `StepInv.noneCov` (a key whose value had no
   entry at R is covered, as every writer since kept it) and `minv_bReadE`
   (the keys after E have no entry).
5. The activation: `BInv.done` (every key passed), `step_bActivate`.
6. No orphans: `SInv.accounted`, `CInv` (a cleanup at its end leaves no entry
   of its generation, and no step puts one), `step_cEnd`.
7. Fresh generations: `SInv.gen_le`, `SInv.mark_lt`, `MInv.bLt`: a live
   generation is at most the latest time, and every other one is before it
   (its deletion committed after it), so the G a creation takes,
   max(1, latest time), is new for a name without a live definition
   (`step_aCreate`, `gen_fresh`).
8. and 9. Builds and cleanups end: liveness, not proved here (section 7).

The step lemmas that commit a transaction are stated over any stream with the
fields the step gives, so that their proofs rewrite with them; the frame
lemmas (`WInv.frame`, `BInv.frame`, `MInv.frameS`) say what a commit keeps of
the threads in flight: a commit writes its keys at the time now + 1, after
every R, so a transaction with one of them in its read set will be refused,
and the other keys keep their values.


## 5. The runs

Two runs (Example.lean) check that the model is not empty, each step's
conditions met by computation (`rfl`, `decide`):

* `example_run`: a database with the value 7 at key 0 and no transaction yet
  creates an index (G = 1), builds it in one step, activates it; a writer
  puts 9 at key 0; the index then has the entry 9 and, by
  `index_is_function` applied to that run, not the entry 7.
* `example_run2`: the same index is deleted; its cleanup scans, deletes its
  one entry, scans from the prefix and finds none, deletes the marker; the
  name is created again with G = 6, the latest time then, and generation 1
  has no entry, no marker and no cleanup left.


## 6. How to check

In the clone (`/Users/f/fl/bench/2026-11-09/clone-l29`), or wherever the
branch is checked out:

    cd lean
    lake build BergDB           # about 5 s from clean, the library alone

and the axioms, from a file outside the library with
`lake env lean Axioms.lean`:

    import BergDB.Index.Example
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
    #print axioms BergDB.Index.example_run
    #print axioms BergDB.Index.example_run2

Each prints `[propext, Classical.choice, Quot.sound]`, or a part of it
(`example_run2`: no `Classical.choice`), 2026-11-09.
`grep -rn sorry lean/BergDB` finds none. The full `lake build` (SIS and the
checker too) was not run in the clone: the library is new and imports
nothing of SIS, and a build of SIS from clean would have loaded the shared
machine; the lakefile's change is the library's entry and its default
target.


## 7. State

**Proved**, for any number of keys, directories, index names, writers,
transactions of any keys, build steps of any size, generations, deletions,
creations again and crashes (also crashes that lose committed
transactions): every invariant of 020-26, section 3 (section 3 above), with
no `sorry`; 2,526 lines. So 020-26's safety results hold beyond its bounds and
beyond its one name, one directory and one key per transaction: no design
fault, for every size, in the protocol as modelled.

**Not proved**:

* **Liveness**: 020-26's BuildEnds, CleanupEnds and NoOrphans (its points 8
  and 9), under fairness. They need a model of fairness (weak fairness of a
  thread's steps, finitely many crashes, writers that may write for ever) and
  a ranking argument: the keys up to E are finitely many; a step in the
  locked phase can be refused only by writers that read their index set
  before the lock was taken, each at most once, as no writer reads a set
  while the build holds the lock. Two points of the model would need care:
  a build step that reads no key and does not reach E (`bRead` allows
  `hi = next`; a step of the code that reads no value meets E and ends the
  build) and data with infinitely many keys (E then need not exist).
  A Lean statement could be: in every fair infinite run with finitely many
  crashes, a definition in state building becomes active or is deleted. Not
  started.
* **What 020-26 left out and this model too**: writes through the Core
  (020-22: undefined), key replace (020-10, section 5.3).
* **The Java code**: the theorems are about the model; the model follows
  020-26's and the code at `83e8e13` with 020-18's fixes
  (`RwEnvironmentImp.indexEntries` for the writers' read sets and the
  per-key index sets). When the code changes the read sets, the lock or the
  order of R and the index set, the model must follow (020-26, section 8).

**How to continue**: liveness, for BuildEnds first (it is what TLC could
check only within small bounds, and where 020-18 found F1 and F4): define
fair runs (`Nat → Sys`), make a build's step read at least one key, and prove
by a ranking on (the keys left up to E, the tries, the writers in flight
when the lock was taken) that a build of a live definition activates it.


Log
===

2026-11-09. Created by coord-1109's agent l29 (17:27), at Frans's word
(17:26), in a clone at `/Users/f/fl/bench/2026-11-09/clone-l29`, branch
`020-29-index-proof`:

* 18:01, `12c8099`: 020-26's model in Lean (one name, one directory,
  transactions of one key), the invariant and its proof, the theorems, the
  run.
* 18:13, `b94a25a`: transactions of any keys.
* 18:27: several index names and directories, with each key's index set
  read under the lock at its own time, as the code does; the proofs per name.
  18:31, on a review of the model against `RwEnvironmentImp.indexEntries`:
  the read set of a transaction has the virtual keys and the keys of its
  object keys only, not of its keys with a suffix (the model asked more of
  the transaction than the code, so it left out some of the code's runs).
  18:37, on a review of the build, the cleanup and the definition changes
  against `IndexBuilderImp` and `IndexManager`: the error steps `bRetry`,
  `bAbort` and `cAbort` (runs of the code the model had not), and G as the
  code takes it, max(1, the latest time), with the freshness invariant
  weakened to match (a live generation at most the latest time).
  18:41: `cut`, reclaim's cut of lookup times; a second run, with the
  deletion, the cleanup and a creation again.

Each step: `lake build BergDB` clean, no `sorry`, the standard axioms only.
Nothing in 2026.4. For the coordinator: a line for this subitem in 020's
readme, Files.
