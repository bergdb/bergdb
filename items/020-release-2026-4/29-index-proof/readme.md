020-29-index-proof
==================

Created 2026-11-09 by Frans Lundberg. Status: open.

A Lean proof, for every size, of the safety invariants of 2026.4's user
indexes that 020-26 checked with TLC within small bounds: the protocol of
020-10 with 020-18's F1, F3, F4 and F5, as 020-26's IndexModel.tla states it
and more (several index names and directories, transactions of any keys), in
Lean, and its invariants proved by induction over the steps. And its
liveness under fairness: cleanups and builds end (020-26's CleanupEnds and
BuildEnds), with the fairness of the index manager's lock that a build needs
when there are several names, and a run that shows weak fairness is not
enough.


Files
=====

On the branch `020-29-index-proof`, in `lean/` (the library `BergDB`, beside
`SIS`, which it does not import; `lake build BergDB` builds it alone, and
`lake build` builds it too):

* `lean/BergDB/Index/Model.lean`. The trusted part: the protocol (section 2).
* `lean/BergDB/Index/Theorems.lean`. The theorems' statements (section 3).
* `lean/BergDB/Index/Inv.lean`. The invariant, its frames (section 4).
* `lean/BergDB/Index/Steps.lean`. A lemma per kind of step, the induction.
* `lean/BergDB/Index/Locked.lean`. A build step's locked phase (section 7.3).
* `lean/BergDB/Index/Liveness.lean`. Runs, fairness, CleanupEnds and
  BuildEnds (section 7).
* `lean/BergDB/Index/Starve.lean`. A run in which weak fairness is not
  enough (section 7.4).
* `lean/BergDB/Index/Example.lean`. Two runs of the model (section 5).
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

From coord-1109 again (18:50): liveness, BuildEnds and CleanupEnds under an
explicit fairness hypothesis on the lock, the weakest that can be justified;
a run of the model in which weak fairness is not enough with several names;
what the Java code would need for the hypothesis to hold, and whether a
starving run can happen in practice with Java's `synchronized`; and 020-26,
section 4, point 8 beyond its core, if time allows. All done (section 7),
with no `sorry`.


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
  only has no R and no read set (`wSuffix`). An `rw()`'s own reads only add
  keys to its read set, so more refusals, which `wDrop` allows.
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
  cut is refused, which `wDrop` and `bRetry` allow). Each step is labelled
  with the thread that takes it, for liveness (section 7.1).
* **Where the model allows more than the code**, so that the theorems hold
  for the code's choices too: a build step reads any range of keys up to E,
  of one key at least (the code: 25 values or 1 MB, or the rest up to E); E
  is any key after which no value has an entry (the code: the directory's
  last key); a cleanup's scan deletes any set of its generation's entries,
  not empty (the code: 100 entries after the last deleted); a writer may
  read the index set of any key, and a transaction in flight may end without
  a commit at any time (`wDrop`: refused, then run again as a new
  transaction, or an exception); a crash may lose committed transactions.
* **Left out**, as in 020-26, section 2.4: writes through the Core (020-22:
  undefined) and key replace (`${transactionTime}`, 020-10, section 5.3).
  Format 1 is in as f with no entry for a value of format 1, as the code
  takes a previous value of format 1; a put of one is refused (`wDrop`) and
  a build over one fails (`bAbort`).

020-26's TLA+ and the Lean model, side by side:

| IndexModel.tla | Model.lean |
|---|---|
| `data`, `def`, `entries`, `markers`, `now` | `Stream`: `data`, `dfn`, `ent`, `mark`, `now`   |
| `ws` of a transaction in flight            | `Stream`: `wk`, `wdef`, `wv` (last write times) |
| `lock`, `mem`, `admin`, `wr`, `bld`, `cln` | `Mem`: the same names                           |
| `WSuffix`, `WStart`, `WReadS`, `WCommit`   | the same; `wReadS` per key                      |
| `WRerun`                                   | `wDrop`, then a new `wStart`                    |
| `ACreate(Map)`, `ADelete(Map)`             | the same, per name                              |
| `BReadE`, `BRead`, `BCheck`, `BCommit`     | the same; `bCheckFail`, `bRefused`              |
| `BLock`, `BActivate`                       | the same; `bActivateFail`                       |
| `CScan`, `CDel`, `CEnd`                    | `cScan`, `cScanEnd`, `cDel`, `cEnd`             |
| `CrashRestart`                             | `crash`, also back to an earlier time           |
| (none)                                     | `bRetry`, `bAbort`, `cAbort`, `cut`             |
| the invariants of its section 3            | Theorems.lean (section 3 below)                 |
| `Fairness`, `BuildEnds`, `CleanupEnds`     | Liveness.lean (section 7)                       |

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
* `gen_fresh` (GenFresh): the G a creation takes, max(1, the latest time),
  is in no marker, entry, build or cleanup of a name without a live
  definition; a live generation is at most the latest time.
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

* `SInv`, of the stream alone, for each name: a live generation at most the
  latest time, a marker's before it; NoStaleEntry; every key covered while
  the index is active; GensAccounted; MarkerNotLive. Being of the stream
  alone, it holds of every stream a crash goes back to, and a start makes
  memory's part anew from it (`minv_restart`).
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
   (if the definition's key was not written after R, G is live: `isLive`
   held after R, `minv_bCheck`) and `StepInv.snap` (a value whose entry the
   step puts is its key's value), `step_bCommit`.
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
8. Builds end: `build_ends`, under fairness, with `locked_phase` for the
   locked phase (section 7.3).
9. Cleanups end: `cleanup_ends`, under fairness (section 7.2).

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

A third, infinite, is section 7.4's (Starve.lean).


## 6. How to check

In the clone (`/Users/f/fl/bench/2026-11-09/clone-l29`), or wherever the
branch is checked out:

    cd lean
    lake build BergDB           # about 6 s from clean, the library alone

and the axioms, from a file outside the library with
`lake env lean Axioms.lean`:

    import BergDB.Index.Starve
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
    #print axioms BergDB.Index.locked_phase
    #print axioms BergDB.Index.cleanup_ends
    #print axioms BergDB.Index.build_ends
    #print axioms BergDB.Index.weak_fairness_not_enough

(Starve.lean imports the rest). Each prints
`[propext, Classical.choice, Quot.sound]`, or a part of it (`example_run2`:
no `Classical.choice`), 2026-11-09, 19:45.
`grep -rn sorry lean/BergDB` finds none. The full `lake build` (SIS and the
checker too) was not run in the clone: the library is new and imports
nothing of SIS, and a build of SIS from clean would have loaded the shared
machine; the lakefile's change is the library's entry and its default
target.


## 7. Liveness

Liveness.lean and Starve.lean: 020-26's CleanupEnds and BuildEnds (its
section 3), whose arguments are its section 4, points 9 and 8, each under
the fairness it needs, stated as hypotheses of its theorem; and a run in
which weak fairness, which 020-26's runs assume, does not give BuildEnds.


### 7.1. Runs and fairness

Each step is labelled with the thread that takes it (`Lbl`): a writer that
begins a transaction (`wbegin`, its choice) or has one in flight (`wr`); a
`w()` of keys with a suffix; a definition change as it begins (`achange`, a
user's call) and its maps (`amap`); a build's step (`bld n g`), its retry
after an exception (`bretry`) and its end without an activation (`babort`);
a cleanup's step (`cln n g`) and its end (`cabort`); a crash; a cut. A run
(`Run`) is an infinite sequence of systems from a reachable one, each a step
of the thread labelled at its time. A thread is enabled where it can step
(`Enabled`). It is weakly fair in a run (`WeakFair`) if, enabled at every
time from some time on, it steps; strongly fair (`StrongFair`) if, enabled
at times without end, it steps. No fairness is asked of a writer's
beginning or of a user's definition change: writers may write for ever, or
never.

Three steps were made as the code is, so that a thread's step moves it on:
a build step reads one key at least (`bRead`; the code's read meets a value
or the end); a cleanup's scan finds one entry at least (`cScan`), or finds
none and ends the cleanup (`cScanEnd`); `wDrop` ends a transaction in
flight. The steps left out (a read of no key, a scan that
deletes nothing, a drop of no transaction) are not the code's, so section 3
holds for the code's runs as before.


### 7.2. Cleanups end (point 9)

`cleanup_ends`: a cleanup that runs at a time ends: at that time or later,
its generation's marker is deleted. Its hypotheses:

* finitely many crashes (a crash starts the cleanup again, and may bring
  back an earlier stream with the marker and its entries);
* the cleanup's thread ends no other way (`cabort`, after an exception: the
  marker stays, and the next start begins the cleanup again);
* weak fairness of the cleanup's thread;
* finitely many entries of its generation at each time.

None on the lock: a cleanup takes none, and it has no read set, so nothing
refuses it. No step but a crash adds an entry to a generation with a marker
(`ent_no_grow`), so the measure, three for each entry left and the
cleanup's phase (`cMeasure`), never grows after the last crash and falls at
each of the cleanup's steps.

```lean
theorem cleanup_ends {sp : Spec V F L} (ρ : Run sp W) {n : Name} {g : Gen}
    (hcr : ∃ N, ∀ j, N ≤ j → ρ.lbl j ≠ .crash)
    (hab : ∀ j, ρ.lbl j ≠ .cabort n g)
    (hwf : WeakFair ρ (.cln n g))
    (hfin : ∀ j, ∃ es : List (Key × L), ∀ k l, (ρ.sys j).st.ent n g k l → (k, l) ∈ es)
    {i : Nat} (hc : (ρ.sys i).m.cln n g ≠ none) :
    ∃ j, i ≤ j ∧ (ρ.sys j).st.mark n g = false
```


### 7.3. Builds end (point 8)

`build_ends`: a build that runs at a time, of a definition in state building
whose definition change is done (no change of its name under way), ends: at
that time or later, the definition is active, or deleted. Its hypotheses,
each a line of the theorem:

1. Finitely many crashes, and finitely many retries of this build
   (`bretry`: a step's try ended by an exception, `DbException` or an
   expired lookup time; the code retries without a bound, after waits).
2. The build's thread ends no other way (`babort`: FAILED, or a stop; the
   definition then stays building until the next start, by design).
3. **Strong fairness of the build's thread**: enabled at times without end,
   it steps. Its steps that need no lock can step at every time until they
   do, so for them this is weak fairness. Its steps that need the manager's
   lock, `isLive` (`bCheck`), the start of its locked phase (`bLock`) and
   its activation, can step only while the lock is free (or, in its locked
   phase, its own): for them it says that a build that waits for the lock
   gets it if the lock is free again and again. This is the fairness of the
   lock.
4. **The lock is free, or the build's, at times without end**: no other
   holder keeps it for ever. A definition change releases it at its maps;
   another build's locked phase at its commit, which comes after finitely
   many refusals (`locked_phase`, below), or at an exception.
5. Finitely many keys with a value at each time (so E exists), and finitely
   many writers, each of which may write for ever.

```lean
theorem build_ends {sp : Spec V F L} (ρ : Run sp W) {n : Name} {g : Gen}
    (hcr : ∃ N, ∀ j, N ≤ j → ρ.lbl j ≠ .crash ∧ ρ.lbl j ≠ .bretry n g)
    (hab : ∀ j, ρ.lbl j ≠ .babort n g)
    (hsf : StrongFair ρ (.bld n g))
    (hlock : ∀ j, ∃ j', j ≤ j' ∧ ((ρ.sys j').m.lock = .free ∨ (ρ.sys j').m.lock = .bld n g))
    (hfin : ∀ j, ∃ e, ∀ k, e < k → (ρ.sys j).st.data k = none)
    (hW : ∃ ws : List W, ∀ w, w ∈ ws)
    {i : Nat} (hb : (ρ.sys i).m.bld n g ≠ none) (ha : (ρ.sys i).m.admin.name ≠ some n) :
    ∃ j, i ≤ j ∧ ¬ Building (ρ.sys j) n g
```

The measure (`bMeasure`): the keys left up to E, each worth more than all of
a step's tries; within a step, its tries left before the locked phase and
its phase; in the locked phase, three for each writer that can commit a
write of an object key (`CanCommitObj`), and three more for a conflict
already there. From the build's read of E on, no step of the run raises it
and each step of the build lowers it (`build_step`): a commit moves the build
on by a key at least; a refusal before the locked phase uses a try; in the
locked phase a conflict comes only from the commit of a writer that could
commit when the lock was taken, whose transaction then ends, and which
cannot read an index set again while the build holds the lock
(`locked_obj_write`, `locked_no_new_writer`). By 3 and 4 the build steps at
times without end, so the measure comes to its end: the activation, or the
deletion.

That is 020-26, section 4, point 8 in full, beyond its core
(`locked_phase`, Locked.lean, done before): the keys up to E are finitely
many; a step refused LockedAfter times runs under the lock, where only the
writers that read the index set before it took the lock can refuse it, each
at most once, and the writes of keys with a suffix never (F1); so a try
commits, and the build moves on.


### 7.4. Weak fairness is not enough

`weak_fairness_not_enough` (Starve.lean): a run of the model with two names,
A and B, over one directory with no data. A is created; its build reads its
end key and its step, and comes to its check (`isLive`), which needs the
lock. Then, round after round for ever: B is created (the lock taken), its
maps (released), its build reads its end key and its step, B is deleted (the
lock taken), its maps (released), B's cleanup finds no entry and ends. Every
thread is weakly fair: each is unable to step at some time of every round
(the builds while a definition change holds the lock, the maps and the
cleanups when there is none, the writer always). The lock is free in every
round; there is no crash, retry or abort; the keys and the writers are
finitely many. So every hypothesis of `build_ends` but strong fairness holds,
and yet A stays building for ever: A's check can step in every round, while
the lock is free, and never does. Weak fairness alone does not give
BuildEnds with several names; by `build_ends`, the run is not strongly fair
for A's build, as the theorem also states.

The starving takes definition changes without end. With finitely many from
some time on, and finitely many crashes and retries, weak fairness of every
build would do, by an argument not written in Lean (section 8): the lock's
other holders are then finitely many builds, each with finitely many locked
steps up to its E, so the lock is free from some time on but in the build's
own locked phase. One name, as in 020-26's runs, is such a case: while its
definition builds, no creation of the name can begin (`aCreate` needs no
live definition), and a deletion ends the build.


### 7.5. The Java code and the lock

The manager's lock is a monitor: `synchronized (lock)` on a plain object
(`IndexManager`). It is taken by every writer, once per object key that its
transaction writes (`getActiveIndexesForDir`, a map read); by a definition
change, for its commit and its maps (`createInner`, `deleteInner`); by a
build, for `isLive` at each step, for its locked phase (`underLock`: a whole
step, its read of up to 25 values or 1 MB, its commit and its tries, after
`LOCKED_AFTER` = 3 refused tries) and for its activation (`activateInner`);
and at the start, and by `job`. Each hold ends (a map read, a commit, a step
whose refusals `locked_phase` bounds), so the lock is free again and again:
hypothesis 4 holds in the code, as long as its threads run.

Hypothesis 3 is what Java does not promise. The Java Language Specification
says nothing of the order in which threads waiting for a monitor get it
(JLS 17.1), and HotSpot's monitors are not fair: a release wakes a waiting
thread, but does not hand it the monitor ("competitive handoff", in
HotSpot's `objectMonitor.cpp`); a thread that comes in the meantime can take
it first, and the woken one waits again. So a build that waits for the lock
has no promise of getting it, however often the lock is free.

What the code would need, one of:

* **A fair lock**: `new ReentrantLock(true)` for the manager's lock, in place
  of the monitor (reentrant as the monitor is, for `isLive` within
  `underLock`). Its waiting threads get it in the order they came, so a
  build that waits gets it after those that waited before it, one hold each:
  a bound, which gives hypothesis 3. Its cost: a release with threads
  waiting hands the lock to the first of them, a wake-up, so when the lock
  is contended the writers' map reads, one per object key, would wait for
  wake-ups that a monitor saves. To be measured before it is chosen
  (`java/stress/performance.sh`, writers on many threads while an index
  builds).
* **A bound on the definition changes while a build waits**: the starving
  run takes them without end (section 7.4). For example, a definition change
  of another name that finds a build waiting for the lock waits until the
  build has had it. Or no change of the code, and a sentence in the Javadoc:
  index creations and deletions in a loop can delay another index's build.
* A bound on retries does not do it. The code bounds the refused tries
  before the locked phase (`LOCKED_AFTER`), and `locked_phase` bounds those
  in it: that bounds the refusals, not the waits for the lock. A bound on the
  retries after exceptions (hypothesis 1) would make such a build FAILED,
  which leaves its definition building until the next start: not an end in
  BuildEnds' sense.

Can a starving run happen in practice with `synchronized`? In principle,
yes: nothing promises otherwise. For ever, no, and for long, rarely: the
build must lose the race for the monitor at every release while it waits.
The model's starving run needs index creations and deletions on other names
without end, one taking the lock each time the build could; a user's loop of
`createIndex` and `deleteIndex` comes nearest, and even then the build gets
the lock at any release that no such call is at the monitor for. Beyond the
model: in the code the writers' map reads take the monitor too (in the
model they are atomic and never hold it), so many threads that write object
keys of indexed directories without a pause meet the build at the monitor at
every release. Their holds are short (a map read) and the lock is free most
of the time, so the build loses a release only to a thread that takes the
monitor in that moment; a long wait needs the lock held almost without a
pause. Not measured for this item.


## 8. State

**Proved**, for any number of keys, directories, index names, writers,
transactions of any keys, build steps of any size, generations, deletions,
creations again and crashes (also crashes that lose committed
transactions), with no `sorry` and Lean's standard axioms only:

* every invariant of 020-26, section 3 (section 3 above): so 020-26's
  safety results hold beyond its bounds and beyond its one name, one
  directory and one key per transaction: no design fault, for every size,
  in the protocol as modelled;
* CleanupEnds and BuildEnds under the fairness each needs (section 7), with
  020-26, section 4, point 8 in full;
* that weak fairness, 020-26's, does not give BuildEnds with several names:
  a build needs strong fairness of the manager's lock (section 7.4), which
  Java's `synchronized` does not promise (section 7.5).

4,113 lines of Lean (Index/: Model 531, Inv 434, Steps 1,359, Theorems 162,
Locked 159, Liveness 957, Example 117, Starve 386; the root 8).

**Not proved**:

* **NoOrphans** (020-26's third liveness property, the entries of a
  generation that is not live are deleted) as a theorem of its own. It
  follows from `cleanup_ends` and `gens_accounted` for a generation whose
  cleanup runs: once its marker is deleted, an entry of it would have to be
  live. A marker without a running cleanup is one between a deletion's
  commit and its maps, which start it, or after a cleanup's `cabort`, until
  the next start.
* **Weak fairness with finitely many definition changes** (section 7.4): an
  argument in words.
* **Hypothesis 4 from the other threads' fairness**: that every holder of
  the lock releases it (a definition change by weak fairness of its maps,
  another build's locked phase by `locked_phase` and its weak fairness) is
  an argument in words; `build_ends` takes it as a hypothesis.
* **What 020-26 left out and this model too**: writes through the Core
  (020-22: undefined), key replace (020-10, section 5.3).
* **The Java code**: the theorems are about the model; the model follows
  020-26's (from the code at `83e8e13` with 020-18's fixes) and the code at
  `b0eba12` (main, 2026-11-09), read for this item:
  `RwEnvironmentImp.indexEntries` (the writers' read sets, the index set per
  key), `IndexBuilderImp` (the build, its tries and errors) and
  `IndexManager` (G, the definition changes, the cleanup, the lock). When
  the code changes the read sets, the lock or the order of R and the index
  set, the model must follow (020-26, section 8).

**How to continue**: for Frans, the choice of section 7.5 (a fair lock, a
bound on definition changes while a build waits, or a sentence in the
Javadoc), with the measurement it needs. In Lean, in order of use: NoOrphans
as a corollary; hypothesis 4 from the weak fairness of the definition
changes' maps and of the other builds; BuildEnds under weak fairness when
the definition changes are finitely many. Each reuses `build_step`,
`descent` and `locked_phase`.


Log
===

2026-11-09. Created by coord-1109's agent l29 (17:27), at Frans's word
(17:26), in a clone at `/Users/f/fl/bench/2026-11-09/clone-l29`, branch
`020-29-index-proof`:

* 18:01, `12c8099`: 020-26's model in Lean (one name, one directory,
  transactions of one key), the invariant and its proof, the theorems, the
  run.
* 18:07, `b94a25a`: transactions of any keys.
* 18:31, `96d9ab0`: several index names and directories, with each key's
  index set read under the lock at its own time, as the code does; the
  proofs per name. Before it, on a review of the model against
  `RwEnvironmentImp.indexEntries`: the read set of a transaction has the
  virtual keys and the keys of its object keys only, not of its keys with a
  suffix (the model asked more of the transaction than the code, so it left
  out some of the code's runs).
* 18:38, `63f3ae5`: on a review of the build, the cleanup and the
  definition changes against `IndexBuilderImp` and `IndexManager`: the error
  steps `bRetry`, `bAbort` and `cAbort` (runs of the code the model had
  not), and G as the code takes it, max(1, the latest time), with the
  freshness invariant weakened to match (a live generation at most the
  latest time).
* 18:42, `d5ba3c0`: `cut`, reclaim's cut of lookup times; a second run, with
  the deletion, the cleanup and a creation again.
* 18:50, `65a598b`, `4abe7eb`: this readme (the TLA+ model and the Lean
  model side by side; liveness, and why several names need strong fairness
  of the lock); Locked.lean, `locked_phase`: the heart of point 8.
* 18:50: coord-1109's second request (section 1).
* 19:04, `d8b5d1b`: the steps labelled by thread; runs, weak and strong
  fairness; `cleanup_ends`. A build step reads one key at least, a cleanup's
  scan finds one entry at least, `wDrop` ends a transaction in flight, as in
  the code (section 7.1).
* 19:16, `e22da73`: `build_ends`, with its measure and `build_step`.
* 19:23, `efd4d28`: Starve.lean, `weak_fairness_not_enough`.
* 19:25, `3882a47`: no unused section variables in Liveness.lean.
* 19:40: this readme: section 7, the State.

Each step: `lake build BergDB` clean, no `sorry`, the standard axioms only.
Nothing in 2026.4. For the coordinator: a line for this subitem in 020's
readme, Files.
