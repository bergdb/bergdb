020-26-index-model
==================

Created 2026-11-09 by Frans Lundberg. Status: open.

A formal model of the user indexes of release 2026.4, their maintenance by
writers and their jobs (020-10, sections 4 to 6, with 020-18's F1 to F5),
checked by machine with the TLC model checker: to find design faults, and
to state the invariants that the design keeps.


Files
=====

* [IndexModel.tla](IndexModel.tla). The model, in TLA+ (section 2).
* [mkcfg.py](mkcfg.py). Writes the configurations of the runs into
  `cfg/` (not kept here; `python3 mkcfg.py` makes them): `d*` the daytime
  runs, `n*` the night runs, `l*` the liveness runs, `min-*` and `sim-*`
  the planted faults (section 6). Each run's bounds are its arguments.
* [run.sh](run.sh) runs TLC on one configuration, `sh run.sh cfg/NAME.cfg
  [WORKERS] [TLC OPTIONS]`, its log in `logs/NAME.log`;
  [queue.sh](queue.sh) runs several, one after another, each stopped after
  a time, `sh queue.sh MINUTES WORKERS cfg/A.cfg ... [-- TLC OPTIONS]`, and
  appends a line per run to `results.tsv`; [night.sh](night.sh) is
  tonight's list (section 8); [trace.py](trace.py) prints a log's
  counterexample as its steps and what each changed.
* [results.tsv](results.tsv). A line per run: the configuration, the
  result, the distinct states, the depth, the time, when.
* The scripts take TLC from `tools/` beside them: `tla2tools.jar` 1.7.4
  from tlaplus's GitHub release, SHA-1
  `bee4a54f3ee3d4afc347c3240ec2d9e93b075104` as its release notes give it,
  run with the JDK at `/opt/homebrew/opt/openjdk`. The runs of this item
  were made in `/Users/f/fl/bench/2026-11-09/m26/`, which has the jar, the
  configurations and the logs; run them there.


## 1. The request

From coord-1109 (2026-11-09, 12:41, at Frans's word of 12:40): a formal
model of 2026.4's index maintenance and build jobs, checked by machine, to
find design faults and to state the invariants. TLA+ with TLC first, for
the protocol: writers (transactions with a read time, conflicts by key and
by virtual hashes), build steps, activation, deletion, cleanup, crash and
restart, lookups at a time. The property: at every lookup time, an active
index's entries equal the function of the data, and no stale entry is
visible; builds and cleanups end, under fairness. A violation is checked
against the Java code before it is called a fault. No change to BergDB.


## 2. The model

From the code at `83e8e13` (main, 2026-11-09), with 020-18's five fixes:
`IndexManager`, `IndexBuilderImp`, `RwEnvironmentImp`, `RwTransaction`,
`WTransaction`.

### 2.1. The state

* **The stream**, the Core's state at the latest time: the data of one
  directory (object keys and keys with a suffix, each with no value, a
  `String` "s" or one of two objects "a" and "b"); the definition of one
  index name (none, or its generation G, its function and its state,
  building or active); the entry keys, triples (G, level, key); the
  markers of deleted generations; the latest transaction's time.
* **Memory**, lost at a crash: the index manager's lock and its maps for
  the name; a definition change between its commit and its maps; each
  writer's transaction in flight; each build thread and each cleanup
  thread, by generation.
* **The index function** f (020-10, section 3.3), two of them, chosen at
  each creation: under function 1 "a" has the level 1 and "b" the level 2;
  under function 2 "a" has the level 1 and "b" none (a field absent); "s",
  no value and every key with a suffix have none under both. So a write
  can give a key an entry, change its level, or take it away.

### 2.2. The Core's conflict check

A transaction has a read time R and a read set, and the Core refuses it
(it runs again) if a transaction that committed after R wrote a key of
its read set (`Db.stmCheckConflicts`). The model keeps no history: each
transaction in flight notes the keys of its read set that commits write
after its R, and is refused at its commit if it noted any; what it reads
at R it takes into its own state when R is fixed. As every state of the
stream is the latest once, and the stream only grows, an invariant of the
latest state holds at every lookup time. Keys are exact, not hashes: a
collision of hashes only refuses more transactions.

### 2.3. The steps, against the code

Each step is atomic; the steps of one thread interleave with every other
thread's at the points where the code allows it: 020-10, section 9.2's
hooks and more.

* `WSuffix`: a `w()` at a key with a suffix: no R, no read set, no lock.
* `WStart`, `WRerun`: R fixed (`fixReadTime`, or the action's first
  read); the previous value is the one at R.
* `WReadS`: the virtual key into the read set; S read under the lock
  (`getActiveIndexesForDir`).
* `WCommit`: the previous value's key in the read set if S has an index;
  f(old) deleted, f(new) put; refused: it runs again.
* `ACreate`: under the lock, G, the definition (building) and the virtual
  key in one transaction. `ACreateMap`: the maps; the lock released; the
  build's thread started.
* `ADelete`: under the lock, the definition deleted, the marker put, the
  virtual key written. `ADeleteMap`: the maps; the lock released; the
  cleanup's thread started.
* `BReadE`: `lastKeyOfDirectory()`, once per build (020-18, F4).
* `BRead`: the step's `getMany` at its R: at most StepMax values after the
  last key, up to E.
* `BCheck`: `isLive`, under the lock (reentrant in the locked phase); a
  deleted index's build ends, FAILED.
* `BCommit`: the step's transaction, its read set the definition's key and
  the keys of the values whose entries it puts (F1); refused LockedAfter
  times, the locked phase. `BLock`: `runStep`'s locked phase, the lock
  held for the tries that follow.
* `BActivate`: `IndexManager.activate`, under the lock.
* `CScan`, `CDel`, `CEnd`: the cleanup, a scan after the last key deleted
  (F5), the deletion; when none is left after it, a scan from the prefix,
  then the marker's deletion.
* `CrashRestart`: a crash or a stop, then `IndexManager.start`: the maps
  from the stream, a build per definition in state building, a cleanup per
  marker.

A thread's start is not a step of its own: its first step comes when it
comes, after any steps of others, as `CREATE_BEFORE_BUILD` lets it (020-18,
interleaving 14). A crash keeps every committed transaction. A crash that
loses a suffix of them, which the crash contract allows (levels.md,
section 8; 020-15's KR-O1), leaves a stream that the same run had earlier,
and a start reads only the stream, so a crash at that earlier point gives
the same states.

### 2.4. What the model leaves out

* More than one index name, more than one directory, subdirectories, and
  transactions that write more than one key: each key's maintenance is
  independent of the others' in the code, and a transaction that reads the
  index set once per key is refused by the same virtual key if the set
  changed after its R.
* Writes through the Core (020-22: undefined, with the scan's check as the
  floor), key replace (`${transactionTime}`, 020-10, section 5.3, whose
  known stale entry the scan's check hides), reclaim's cut of lookup
  times, refusals by the Core (`DbException`), expiries, interrupts,
  `Error`s that fail the database, and format 1.
* The values' contents and the levels' encodings (020-16 fuzzes them), the
  1 MB of a step (in StepMax), the pauses, a job's status and `join()`.
* Scans: the model checks the raw entries, which is stronger, as a scan
  skips a stale entry (020-10, section 3.4).
* With a finite number of keys a build cannot chase appending writers, so
  F4's fault (a build that never ends) is out of reach; F4's end key is
  checked for safety (`BuildCovers`, and the planted fault `NoEndKey`).


## 3. The properties

Invariants, of every reachable state, so at every lookup time:

* **IndexIsFunction**, the main property (020-10, sections 3.4 and 9.1;
  020-22's V3): if the definition is active, the entries of its generation
  are exactly f over the directory's values: none missing, none stale.
* **NoStaleEntry**: while the index is building too, every entry of its
  generation is f of its key's value.
* **BuildCovers** (020-22's V3 while building; 020-18's F4): for a build
  that runs, every key it has passed, and every key after its end key E,
  has its entry exactly.
* **GensAccounted** (020-22's V8): every generation that has entries is the
  live definition's or has a marker, so no entry is out of every cleanup's
  reach.
* **MarkerNotLive** (V7) and **StartAccepted** (020-10, section 4.5): no
  marker names the live generation, and no start refuses the database.
* **GenFresh** (020-10, section 4.3): every creation's G differs from every
  G before it, with G as the latest transaction's time (`TimedGen`).
* **MemAgrees** (020-10, section 5.2): when no definition change is under
  way, the manager's maps are the stream's definition.
* **LockSane**: the lock is held only by a definition change or by a build
  in its locked phase.

Liveness, under fairness (a transaction that began runs to its commit or
its rerun; a started thread goes on; writers need not begin transactions,
and may begin them for ever), with at most MaxCrashes crashes:

* **BuildEnds**: an index in state building becomes active or is deleted.
* **CleanupEnds**: every marker is deleted.
* **NoOrphans**: the entries of a generation that is not live are deleted.


## 4. Why they hold

The argument that the runs check, for any number of keys and writers; the
model checker checks it within the bounds of section 5. Let G be a
generation, created by a transaction at time t_c and deleted by one at t_D
(or never); G's life is (t_c, t_D).

1. **A writer that commits in G's life keeps G.** If its R is before t_c,
   the creation's write of the directory's virtual key refuses it. So R is
   at or after t_c, and it read S after R, under the lock, which the
   creation held from before its commit until its maps had G: S has G. It
   read the key's previous value at R with the key in its read set, so
   that value is the key's value just before its commit. It deletes f(old)
   and puts f(new): if G's entries of the key were f(old) or none, they
   are now exactly f(new).
2. **No writer writes G after t_D.** One that had G in S read S before the
   deletion's maps changed, so its R is before t_D, and the deletion's
   write of the virtual key refuses it.
3. **A build step commits only in G's life, and puts only exact entries.**
   A deletion before its R fails its `isLive` check (the deletion's commit
   and maps are in one hold of the lock); one after its R refuses it (the
   definition's key is in its read set). It puts f(v) only for a key whose
   value v at R has an entry, with the key in its read set, so v is the
   key's value at the commit. Keys whose values have no entry are not in
   its read set (F1), as the step writes nothing for them.
4. **Coverage.** From 1 and 3, G's entries are never stale (NoStaleEntry).
   A key the build has passed is exact: the step put its entry, or it had
   none at R, and every later writer keeps it (1). A key after E is exact:
   E was the directory's last key when read, after t_c, so the key got its
   value from a writer in G's life (1); that is F4's argument
   (BuildCovers).
5. **The activation.** The build activates after the step that met the end
   of its keys up to E, so every key is exact then, and writers keep them
   so (1) until t_D: IndexIsFunction. A crash keeps the stream; the
   restarted build passes the keys again, putting entries that are there.
6. **No orphans.** G's entries are put only in G's life (2, 3). The marker
   is put at t_D and deleted only after a scan from the prefix found no
   entry of G after t_D, and none comes later: GensAccounted.
7. **Fresh generations.** G is the latest transaction's time when the
   creation runs under the lock; a creation of the name after a deletion
   runs after t_D, which is after the old G (020-10, section 4.3).
8. **Builds end.** The keys up to E are finitely many. A step refused
   LockedAfter times runs under the lock, where only the writers that read
   S before it took the lock can refuse it: writers of object keys read S
   under the lock, and the writes that take no lock (keys with a suffix)
   are in no step's read set (F1). Each of those writers commits, or is
   refused, at most once more, and then waits for the lock to read S
   again; so a try commits.
9. **Cleanups end.** A cleanup has no read set, so nothing refuses it, and
   no entry of G is put after t_D (6).

The planted faults of section 6 take out each of these mechanisms in turn.


## 5. The runs

Breadth-first, every reachable state, on F53 shared with other sessions
(load 15 to 32 on 10 cores), 4 workers. The bounds are those named, and
else: object keys 1 and 3, 1 writer, function 1, the values "s", "a" and
"b", 1 creation, steps of 1 value (StepMax), cleanup steps of 1 entry,
the locked phase after 1 refusal (LockedAfter), no crash. "A suffix key"
is key 2, between them, with a suffix. Every invariant of section 3 holds
in every state of every run below:

| Run                 | Bounds                                 | States     | Depth | Time  |
|---|---|---|---|---|
| `d1-crash`          | 2 keys, 1 crash                                | 2,415,244  | 36 | 41 s |
| `d3c-writers-1key`  | 1 key, 2 writers, 1 crash                      | 4,167,820  | 31 | 66 s |
| `d2c-recreate-1key` | 1 key, functions 1 and 2, 2 creations, 1 crash | 50,844,430 | 44 | 597 s |
| `d5-step2`          | 2 keys, a suffix key, steps of 2               | 7,749,300  | 41 | 85 s |
| `d4d-timed-small`   | G a time; 1 key, 2 creations, 1 crash          | 11,870,108 | 36 | 145 s |
| `d6-none`           | 2 keys, a suffix key, 1 crash                  | 8,324,896  | 38 | 60 s |

`d3c` counts states up to symmetry (the two writers are
interchangeable); `d5` has LockedAfter 2; `d4d` has the value "a" only
and at most 8 commits (TimedGen, so GenFresh is checked with G the latest
transaction's time).

The liveness properties of section 3 hold, under fairness, in every
behaviour of:

| Run                     | Bounds                                  | States    | Depth | Time    |
|---|---|---|---|---|
| `l1-live`               | 2 keys, a suffix key                   | 4,162,448 | 38 | 832 s |
| `l4-live-1key-recreate` | 1 key, value "a", 2 creations, 1 crash | 1,949,904 | 44 | 1,370 s |
| `l4-live-1key-2w`       | 1 key, 2 writers, value "a", 1 crash   | 449,476   | 31 | 60 s |

Stopped at their time limit or by hand, with no violation in the states
they reached (for tonight, section 8):

| Run                     | Bounds                                     | States reached | Depth |
|---|---|---|---|
| `d2-recreate`           | 2 keys, functions 1 and 2, values "a" "b", 2 creations | 20,863,415 | 25 |
| `d2b-recreate`          | as `d2-recreate`, steps of 2, cleanup steps of 2       | 9,730,439  | 23 |
| `d3-writers`            | 2 keys, 2 writers                                      | 12,534,109 | 20 |
| `d4c-timed-1key`        | G a time; 1 key, values "a" "b", 2 creations, 1 crash  | 73,745,822 | 33 |
| `l3-live-1key-recreate` | 1 key, values "a" "b", 2 creations, 1 crash (liveness) | 1,120,994  | 23 |

Random simulation of the whole model (`sim`: 2 writers, keys 1 and 3 and
the suffix key 2, functions 1 and 2, the values "s", "a" and "b", 2
creations, 1 crash; TLC's `-simulate`, traces of up to 100 steps):
no violation in 15 minutes, 857 million states checked along random
traces, 4 workers; and earlier, 100,000 traces of up to 80 steps, 16
million states. The same simulation with each change that safety does not
need (`NoEndKey`, `NoFinalCheck`, `AllHashes`), 50,000 traces each: no
violation.


## 6. The planted faults

Each mechanism of the design taken out in turn (`Bug` in the
configuration). The first nine break safety: the shortest counterexample,
breadth-first with one worker (`min-*`, at the default bounds, with 2
writers for `NoPrevHash` and 1 key and 2 creations for `ConstGen`), each
found in under 5 seconds; the whole model's random simulation (`sim-*`)
found each too, within 2 seconds. The last two break liveness (`l1-live-*`,
at `l1-live`'s bounds; for `NoLockedPhase` without the suffix key), each
found in under 2 minutes as a lasso, a cycle the build never leaves.

| Fault           | Taken out (020-10's section, or the change)        | Broken first  | Steps |
|---|---|---|---|
| `SBeforeR`      | R fixed before S is read (5.1, step 1; 015-43)      | BuildCovers   | 7 |
| `NoVhash`       | the virtual key in a writer's read set (step 2)     | BuildCovers   | 7 |
| `NoLock`        | S read under the manager's lock (5.2)               | BuildCovers   | 7 |
| `NoPrevHash`    | the previous value's key in the read set (step 4)   | NoStaleEntry  | 9 |
| `NoDefHash`     | the definition's key in a step's read set (6.1)     | GensAccounted | 14 |
| `NoIsLive`      | a step's `isLive` check (6.1)                       | GensAccounted | 14 |
| `NoValueHash`   | the keys of a step's values in its read set (6.1)   | NoStaleEntry  | 13 |
| `ConstGen`      | a new G for each creation (4.3)                     | MarkerNotLive | 6 |
| `NoActCheck`    | the activation's check that the index is live (6.1) | MarkerNotLive | 10 |
| `NoLockedPhase` | a step's locked phase (`runStep`, the review of I1) | BuildEnds     | lasso |
| `AllHashes`     | F1: every key a step read in its read set           | BuildEnds     | lasso |

What each counterexample does:

* `SBeforeR`, `NoVhash`, `NoLock`: a writer reads the index set without
  the new index (before the creation; or, without the lock, between the
  creation's commit and its maps) and commits after the creation without
  being refused, so its key, after the build's end key, has no entry.
* `NoPrevHash`: two writers of one key read the same previous value (none);
  one puts "a" and its entry, the other deletes the key and deletes the
  entry of what it took as the previous value (none), so the entry of "a"
  stays, stale.
* `NoValueHash`: a step reads "a"; a writer deletes the key (and its
  entry) before the step commits; the step puts the entry of "a", stale.
* `NoDefHash`, `NoIsLive`: a step passes its check, or reads after the
  deletion without the check; the deletion commits, its cleanup finds
  nothing and ends; the step then commits its entry into the deleted
  generation, which no definition and no marker names: an orphan.
* `ConstGen`: a creation after a deletion takes the deleted generation's
  G, which its marker names: a start would refuse the database
  (StartAccepted), and the cleanup would delete the live index's entries.
* `NoActCheck`: the index is deleted between the build's last step and its
  activation, which then writes the definition again, active, with the
  marker of its generation still there.
* `NoLockedPhase`: the writer writes the step's key between its read and
  its commit at every try, for ever, so the build never ends (the review
  of I1's "BUILDING after 30 s").
* `AllHashes`: in the locked phase, the build's step has the key with a
  suffix in its read set, and the writer rewrites that key, which takes no
  lock, at every try: the build never ends, holding the lock, so every
  writer of an object key waits. This is 020-18's F1, found here by the
  checker from the code before F1.

Three changes do not break safety: `NoEndKey` (F4's end key; without it a
build reads to the directory's end at each step), `NoFinalCheck` (the
cleanup's last scan from the generation's prefix) and `AllHashes`. Each
was simulated without a violation (50,000 traces of the whole model, 4.1
million states each), and each keeps every invariant in every state at
`d6-none`'s bounds: `d6-NoEndKey` 4,388,496 states, `d6-NoFinalCheck`
8,963,712, `d6-AllHashes` 8,784,040. So F4 and F1 are fixes of liveness
and cost, as 020-18 says, and the last scan from the prefix is redundant:
by section 4, point 6, no entry of a deleted generation is put after its
deletion, so the scans after the last key deleted have found them all.


## 7. Findings

1. **No design fault found.** Within the bounds of section 5, the design
   of 020-10 with 020-18's F1, F3, F4 and F5, as the code at `83e8e13`
   does it, keeps every invariant of section 3: at every lookup time an
   active index's entries are exactly f over the directory's values; no
   entry of a live generation is ever stale, also while it builds; no
   entry is out of every cleanup's reach; no marker names the live
   generation, so no start refuses the database; every creation's G is
   new. Builds and cleanups end under fairness, with writers that write
   for ever. So there was no violation to check against the Java code, and
   no test or probe was written.
2. **Each mechanism is needed.** Each of nine planted faults breaks safety
   in 6 to 14 steps, and two more break liveness (section 6): R before S,
   the virtual key, the lock, the previous value's key, the definition's
   key and `isLive` in a step, the values' keys in a step, a new G per
   creation, the activation's check, and the locked phase. Section 4 says
   which point of the argument each serves. The checker found 020-18's F1
   again from the code before F1, as a lasso.
3. **Three mechanisms are not needed for safety.** F4's end key and F1's
   smaller read set serve liveness and cost only, as 020-18 says. The
   cleanup's last scan from the prefix (F5) is redundant for the Pub
   layer's own writes (section 6). It costs one scan per cleanup, and it
   would also catch an entry of the deleted generation that a write
   through the Core (undefined, 020-22) put behind the cleanup's position.
   No change proposed.
4. **The invariants** the indexes rely on are section 3's, with the
   argument of section 4: V3 of 020-22, section 4.2, in its strong form
   (equal to f while active, within f while building, exact for the keys
   a build has passed and those after its end key E), V7 and V8, and
   020-10, section 4.3's fresh G and 5.2's memory and stream.
5. **Documents, not code.** 020-10, sections 6.1 and 6.2, still describe the
   build and the cleanup before 020-18's F1, F3, F4 and F5: "the values'
   hashes are in the read set", a step of "at most 25 values", a build
   from the first key to the directory's end, a cleanup "under the
   generation's prefix" (020-18, section 4, left it to the coordinator).
   The model follows the code.


## 8. What is left

* **Tonight's runs** (`night.sh` in `/Users/f/fl/bench/2026-11-09/m26/`,
  one JVM, 8 workers, a heap of 12 GB, each run stopped at its cap, a
  line per run in `results.tsv`):
  * Part 1, at most 3 h 45 min, likely 1 to 3 h: `sh night.sh 1` runs
    `d2-recreate` (2 keys, 2 creations; 90 min cap), `d3-writers` (2 keys,
    2 writers; 90 min) and `d4c-timed-1key` (45 min), the runs stopped
    today. They grew to 21, 13 and 74 million states in 5, 3 and 15
    minutes on a loaded machine; each is expected to end within its cap
    on a quiet one, not certain.
  * Part 2, at most 4 h 30 min: `sh night.sh 2` runs `n1-all-1w` (the
    whole model with 1 writer: 2 keys and a key with a suffix, functions
    1 and 2, 2 creations, 1 crash; 120 min cap, likely stopped at it), the
    liveness runs `l3-live-1key-recreate` (1 key, values "a" and "b", 2
    creations, 1 crash) and `l3-live-1key-2w` (1 key, 2 writers; 60 min
    each), and 30 minutes of random simulation of the whole model with 2
    writers (`sim`, traces of up to 120 steps).
  * A stopped run says only that no violation is in the states it
    reached; `results.tsv` gives the states and the depth.
* **Not modelled** (section 2.4): two names, two directories, transactions
  of several keys, refusals and failed builds (a FAILED build leaves its
  definition building until the next start, by design: BuildEnds assumes
  none), key replace, writes through the Core, reclaim. Two names and
  transactions of several keys are the next extensions, if wanted: the
  argument says each key's maintenance and each generation are
  independent, and the model would check it.
* **A proof for any size.** Section 4's argument holds for any number of
  keys, writers and generations; the runs check it only within their
  bounds. A Lean proof of it (the transition system and the invariants of
  section 3 as an inductive invariant) is possible, not started.
* **When the code changes**, the model must follow: 020-18's F3 rest (a
  locked step's reads moved out of the lock), O1 (one thread for all
  builds and cleanups), or any change of the read sets, the lock or the
  order of R and S. Then `python3 mkcfg.py` and `sh queue.sh` again.


Log
===

2026-11-09. Created by coord-1109's agent m26 (12:41), at Frans's word
(12:40). The model from 020-10, 020-18 and the code at `83e8e13`; TLC
1.7.4 downloaded and its SHA-1 checked against the release notes. Runs
from 12:57 to 15:11 on F53, one JVM at a time, 4 workers, under the day's
load (sections 5 and 6): no design fault; each of the eleven planted
faults found; the larger bounds left for tonight (section 8). Nothing of
BergDB changed; nothing staged or committed. For the coordinator: a line
for this subitem in 020's readme, Files.
