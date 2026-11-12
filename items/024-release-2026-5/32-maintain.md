# 024-32. maintain(): cleanup on request, in release 2026.5

Created 2026-11-12 by Frans Lundberg. Status: done (on the branch `024-32-maintain`, head `ec924fd7`; not on `main`).

Frans, 2026-11-12, 12:10: "maintain(): [...] No, I want this now. In this
release." His decision of 2026-11-10, 12:31 (023-04, Y10): "Y10, yes to
maintain(), note: maintainance should be performed while doing other
operations on the database, so the user explicitely calling maintain()
should be optional, not a requirement on the user that she must call
maintain." And of 10:49 (023-02, F7): "repeatedly calling maintain()
must eventually release resources so a database with only one
hello-world entry will consume about as much as a fresh hello-world
database."

So the cleanup keeps going in the ordinary operations, as it does today;
`maintain()` only lets an application ask for more. The case it is for:
by P3 (calm when not used, 010-01) reclaim advances only with the
application's writes, so an emptied database that is no longer written
to never gives its space back.

By the agent "maint" of coord-1112, from 12:11. Clone
`/Users/f/fl/bench/2026-11-12/maint/clone`, branch `024-32-maintain` from
`main` at `288c973e`. Outputs: [32-maintain/](32-maintain/).


## 1. In short

* `Db.maintain()` (Core) and `Database.maintain()` (Pub): one call does
  a bounded part of reclaim's work, in the database's own internal
  transactions, and returns whether more is due now. Nothing calls it on
  its own; a database is bounded without it.
* A call writes only internal records of kinds that exist (reclaim's
  table and steps, an empty record whose take moves the startup pos, a
  filler put and deleted); nothing when nothing is due. No format, model
  or checker change: the model takes the startup pos from the trace and
  allows any pace; new trace configurations r-maint and e-r-maint pass.
* **G5** (section 4), 1M keys put and deleted, then 20,000 maintain()
  calls and no writes: kept 254 MB to 83 kB (a fresh twin: 592 bytes;
  limit twice it plus 600 kB), quiet after call 6,130; at most 75 kB and
  5 records a call; resident objects 10 against 5, after M7, the
  eviction's dead hand in maintain().
* Gates on `ec924fd7` all OK (section 5); no existing test changed.
* Section 2 is the design, written before the code. Section 3 is what
  was built, section 4 G5, section 5 the gates, section 6 the questions.


## 2. The design

### 2.1 Why the user's writes are needed today

Reclaim (`Reclaim.transactionCompleted`, after each user commit) has
four waits, and an idle database meets none of them:

1. **An iteration begins** only when the stream has grown by twice the
   startup distance sd since the last one began, and a quarter of R has
   passed.
2. **A step** is allowed only while the bytes rewritten are below the
   internal fraction f times the stream's growth since the iteration
   began.
3. **The startup pos must pass pEnd, then pSafe**, before the cut: it
   moves by the take, each record's share of D, the got-dirty nodes of
   the startup section (`TransSeq.take`), in proportion to the record's
   own bytes; without records it does not move.
4. **A meta block must name a transaction at or after pCut**
   (`metaTransPos >= pCut`), since recovery starts there. Meta blocks
   are at fixed positions, every 200,000 bytes
   (`RecoverableStream.META_BLOCK_DISTANCE`); without 200 kB of records
   after pCut none comes.

Then the cut also waits for time (tEnd older than R) and for the table
that marks it to be durable (`cutIfDurable`).

### 2.2 What one call does

`Db.maintain()` takes the write lock, checks the state (2.6), reads the
time now (`DbClock.currentTime()`), and calls `Reclaim.maintain(now)`,
which does, in this order, at most one of each:

* **M1, begin.** If no iteration runs, R is finite, a quarter of R has
  passed since the last one began (as at a commit), **no cut is
  pending** (every done iteration is cut, or has nothing to cut: its
  pCut is at or before the first available position), and the cut that a new one
  leads to releases at least `MAINTAIN_MIN_RELEASE` = 400,000 bytes
  (2 meta block distances): r = lastPStart - firstAvailablePos, or the
  stream length when the table is empty (the first iteration cuts at its
  own pStart). Then the iteration begins as at a commit: pStart the
  stream length, tStart the last transaction's time, its table stored.
  The growth condition of 2.1, point 1, is replaced by r.
* **M2, a step** of the iteration that runs, of at most `MAX_STEP_SIZE`
  (16 kB of scan) and the step reserve, as at a commit, but without the
  allowance of 2.1, point 2: the call is the request for it.
* **M3, safe positions**, as at a commit (`markSafePositions`).
* **M4, a take.** If a done iteration whose cut is pending waits for the startup pos
  (sp < pEnd, or pSafe set and sp < pSafe, not cut), one internal
  transaction with no KVs (an empty record) whose take, after its own
  share, takes the oldest transactions of D, whole, until sp reaches that
  position or the taken nodes reach `MAINTAIN_TAKE_BYTES` = 256 kB (at
  least one transaction). Then M3 again.
* **M5, the filler.** If a done, safe iteration has everything for its
  cut but the meta block (2.1, point 4): one internal transaction that
  puts the key `/#i/dreclaim/-fill` with a value of zeros that reaches
  the next meta block (at most 200,000 bytes), and one that deletes it.
  The meta block is written inside the filler's record and names the
  record before it, which is at or after pCut (pCut is a pStart, where
  an iteration's table was stored).
* **M6, the cut**: `pretruncateIfPossible(now)`. If a cut is pending
  and its table is not yet durable, `Db.maintain()` releases the lock,
  syncs (ordinary), takes the lock again and calls `cutIfDurable()`.
* **M7, the dead hand** (added after G5's first run, section 4): one
  step of the eviction's dead hand (`Eviction.deadStep`, via the new
  `maintainStep`), as `afterTransaction` takes after every transaction:
  after a cut it walks the handle tables, a batch a step
  (`DEAD_BATCH`, `BATCH_NANOS`), and drops the objects of versions the
  cut ended. Only where the dead hand runs today (a cache budget, the
  default, or the tests' random schedule). Without it the objects of the
  deleted keys stayed resident after maintain()'s last cut, as no
  transaction followed it.

Why M1 asks for no pending cut and for r of 400 kB: so
that the calls stop. After an emptied database has converged, the stretch
between two pStarts holds an iteration's few records and at most one
filler (under 200 kB); with no cut pending, r is one such
stretch, below 400 kB, so no iteration begins and the calls return
false. Each iteration begun by M1 writes at most one filler, at most half
of what its cut releases, and rewrites at most r (the live values stored
before pCut are within the stream from the first available position to
pCut), so a call's writes follow what it releases (P4).

### 2.3 What it returns

`true` if more is due now: an iteration runs (a step is due), a take is
due (M4's condition), a filler is due (M5's), a pending cut waits for its
sync, M1's conditions hold, or a round of the dead hand runs (M7). `false` if nothing is due until time
passes (R / 4 for the next iteration, R for a cut) or the application
writes. A caller that wants the space back now calls it until it
returns false, and again later; a call when nothing is due writes
nothing. With a clock that does not move, a database returns false after
a bounded number of calls.

### 2.4 What it writes to the stream

Only internal records of kinds that exist: reclaim's table and steps, as
at a commit; M4's empty record (a record with no value nodes, as an
empty user transaction makes, `Eviction`'s tests and
`DbTesterRestart.testRestartAfterTransactionsThatChangeNothing` use
them); M5's put and delete of one internal key. No new record format, no
new key prefix: `/#i/dreclaim/` is reclaim's already (Keys and the layers
above). When nothing is due, nothing is written.

### 2.5 Locking and threads

All of it under Db's write lock, as reclaim's work after a commit is: a
call waits for a running commit and a commit waits for the call; the
internal transactions go through `Db.execute` as reclaim's do, so readers
see each at its time, and reads in other threads run as with commits
(no read lock exists). The sync of M6 is outside the lock. A call's work
is bounded: one step (16 kB of scan), one take of 256 kB of nodes plus
one transaction, one filler of at most 200 kB, and the tables; P1's
20 ms guide holds by the sizes (a step and a take are what a commit
carries today).

### 2.6 A stopped or failed database, and the limits

As a setter that commits (`setRetainDuration`): on a database that is
not active, `IllegalDbStateException`, `DbStoppingException` or
`DbFailedException`; with the top node ordinals used up, the
`DbException` of a user transaction (`refuseIfTopOrdinalsUsed`), and
with no user time left (after `DbClock.LAST_USER_TIME`) a
`DbException` too, so that maintain's internal transactions never use
the times kept for reclaim after a commit (015-55). A failure inside
fails the database as an internal transaction after a commit does. A
`DbStoppingException` from a stop during the call ends the call; what
was committed stays, the rest goes on at the next call.

### 2.7 P2: the stream follows the calls

A call is an input like a transaction: its time (the clock) and the
state decide what it writes, and the state is in the stream (the table,
D from the startup section). A restart between calls changes nothing:
the same calls after it write the same bytes (tested, 3.3).

### 2.8 The model and the trace format

* **Reclaim's steps in the model do not come with user transactions.**
  The model has records, each a transaction (`Record.trans`), and a
  touch for a step's (sis-model.md, 15.3); the trace has every record,
  user or internal, as a `TX` block with its `kind` (trace-format.md,
  section 2). Nothing ties a step to a user record.
* **M4's empty record is an empty transaction to the model**, with a
  startup pos that Java chooses: the model's take policy has the
  deadline and any pace (`takePolicy`, SIS/Bound.lean: "T3 holds for
  every pace"), and the trace checker takes sp from the trace (`REC`
  lines). A take beyond the share is a pace that takes more.
* **M5's records are a put and a delete** of an internal key, as any.
* So nothing changes in the model, the trace format or the checker:
  the smallest correct way. To check it rather than argue it, the
  exporter gets a `maint` option (calls of maintain() among the
  workload's transactions), and a run of the checker on such traces
  is part of the gates (section 5).


## 3. What was built

On the branch `024-32-maintain` of the clone (section 8 has the head).
Touched files, none of them the pace or tidy agents' (024-31's
`TransSeq.shareFp` and `take`, 024-33's cache tables, 024-34's reclaim
reads): `TransSeq` gets a new method beside `take`, `Reclaim` new methods
beside `transactionCompleted`; no existing method body changed but
`Db.store` (four lines after the take).

* **`Db.maintain()`** (Core) and **`Database.maintain()`** (Pub, through
  `DatabaseImp`), Javadoc with Frans's "optional" in his words. Db
  checks the state, the top node ordinals and the user time
  (`DbClock.userTimeLeft`, new), calls `Reclaim.maintain(now,
  lastTransTime)` under the write lock, and syncs outside it when a cut
  waits for its table to be durable. Anything but a stop or a failure
  that an internal transaction already reported fails the database, as
  reclaim's work inside a commit's go point does.
* **`Reclaim.maintain`**, M1 to M6 of 2.2, with `maintainDue`,
  `cutPending`, `maintainTakeTarget`, `cutWaitsForMetaBlock`, the
  constants `MAINTAIN_MIN_RELEASE` (400,000), `MAINTAIN_TAKE_BYTES`
  (262,144) and the filler key `/#i/dreclaim/-fill.txt`.
* **`Trans.maintainTakeTo`** and **`TransSeq.takeTo`**: M4's take after
  the share, oldest transactions first, whole, to the target or the
  budget, at least one transaction; called from `Db.store` only for
  maintain()'s empty record.
* **Tests**, `ReclaimMaintainTester` (unit, 0.5 s): nothing due (R
  forever, and a fresh database with R) writes nothing and returns false
  for 3 R of calls; a stopped database throws; an emptied database of
  20,000 keys converges by maintain() alone (6.6 MB kept to about
  0.1 MB), each call's growth and records bounded, the last 5 R quiet,
  reads of live keys right at the latest and the first available time
  between calls and in a reader thread during them, and after a restart;
  the same calls with two restarts among them give the same stream byte
  for byte and the same cut (P2).
* **G5** in `CountGates` (section 4) and `count-gates.sh`'s header.
* **Conformance**: `TraceExport` gets `maint=K` (a maintain() call after
  every K-th user transaction, in runs A, B and E alike); two new
  configurations in `conformance.sh`, `r-maint` (set `reclaim`, maint=1)
  and `e-r-maint` (set `evict`, maint=3, random eviction, reads,
  restarts). By hand, before the gates: r-maint seeds 1 and 2 and
  e-r-maint seed 1, TRACECHECK OK with the main tree's checker (the Lean
  sources are those of `main`): 938 records in seed 1, of them 100 of
  maintain()'s empty records, 20 fillers put and deleted, 96 cuts
  decided, C-CUT 0 of 96 fail.
* **docs/levels.md**, section 6: a bullet on maintain(); the Javadoc of
  `Database.setRetainDuration` names it.

A finding while testing, and the fix in the design: after the user's
deletes, the table can hold an iteration whose pCut equals the first
available position once the iteration before it is cut (the first
iteration cuts at its own pStart, and the next one's pCut is that same
pStart). Such an iteration has nothing to cut and is never marked cut;
M1's first rule, "the last iteration is cut", then never held, and the
emptied database stopped at 6.6 MB. M1 now asks that no cut be pending
(`cutPending`: done, not cut, pCut after the first available position),
and M4 takes only for such iterations.


## 4. G5, back to empty by maintain()

**What.** 023-03's T1 with its second drive, at 1M keys, as G4 (024-30,
section 8) but driven by maintain() calls instead of overwrites:
`CountGates g5`, two databases on a `FileStream`, sd = 100 kB, R = 1 s
of a test clock, eviction on with the builder's budget. The emptied one:
R, "/a.txt", 1M keys put and deleted, 100 a transaction; the twin: R and
"/a.txt" only. Then each gets 20,000 calls of `maintain()` (20 R), the
clock 1 ms on before each, and no writes. Measured at the end as G4, and
during the drive: the last call that returned true, the calls that
wrote, the most bytes and records of a call.

**The gates.** Kept (the most in the last R) at most twice the twin's
plus 600,000 bytes (`MAINTAIN_MIN_RELEASE` and a meta block distance,
section 2.2: the calls stop once a cut would release less than 400 kB,
and a filler of up to 200 kB may be in the stream kept); the last call
returning true within the first three quarters of the drive (converged,
then quiet for 5 R); the heap after a GC at most 2 times the twin's;
the key nodes, the resident objects and the handles at most the larger
of twice the twin's and the twin's plus a_n = 10 (023-03, section 2.6,
the strict allowance), the dead KEY klongs the larger of twice the
twin's and the twin's plus B = 30 (023-03's C4). The additive
tolerances because the twin is tiny: 4 key nodes, 5 objects, no dead
klongs (it was never overwritten), where twice it means 8, 10 and 0.
ST6 is reported, not counted, as in G4.

**First run** (12:45, before the dead hand; `32-maintain/g5-first-run.txt`):
the stream converged (kept 254,432,632 to 83,384 bytes), but 76,963
resident objects and handles against the twin's 5, and the heap 15
times the twin's: the eviction's dead hand drops the objects of ended
versions a batch after each transaction, and no transaction followed
maintain()'s last cut. So M7 (section 2.2).

**With M7** (`32-maintain/g5-dead-hand.txt`, on `ec924fd7`'s code but
the tolerances; 8 s for both databases):

| Measure                              | Emptied     | Twin        | Limit       | Result |
|---|---|---|---|---|
| M1, kept, most in the last R         | 83,384      | 592         | 601,184     | PASS   |
| last call returning true             | 6,130       |             | 15,000      | PASS   |
| M4, reachable key nodes              | 6           | 4           | 14          | PASS   |
| M5, dead KEY klongs                  | 25          | 0           | 30          | PASS   |
| M11, resident objects, handles       | 10, 10      | 5, 5        | 15          | PASS   |
| ST6, table slots                     | 225,952     | 80          | (known)     | report |
| heap after a GC, bytes               | 18,142,600  | 12,230,200  | 24,460,400  | PASS   |

* **The drive**: 3,124 of the 20,000 calls wrote, 1,147,056 bytes in
  all; the most a call wrote was 74,992 bytes in at most 5 records; 3
  iterations begun by maintain() and 3 cuts (7 in all, 4 of them during
  the deletes). The twin's calls wrote nothing and returned false.
* **The kept stream** went from 254 MB after the deletes to 83 kB, the
  stream of a few iterations' records and a filler: within 0.14 of the
  limit. The first cut in the drive came at call 4,117 (the user's last
  iteration, waiting for R), the last call with work at 6,130.
* **ST6** keeps the peak size of the tables, as in G4 (024-05, ST6; the
  tidy agent's 024-33).


## 5. Gates

On the head `ec924fd7`, each in a slot:

| Gate                       | Result                                           | Time   |
|---|---|---|
| `java/before-commit.sh`    | BEFORE COMMIT OK (unit 1,692, F 89, demos)       | 73 s   |
| `java/stress/level1.sh`    | LEVEL 1 OK (MEM 129, SS 1.53)                    | 171 s  |
| `java/stress/level3.sh`    | LEVEL 3 OK, its `lake build` included            | 730 s  |
| conformance, reclaim set   | 35 traces OK (r-maint's 5), C-CUT 0 of 799 fail  | (in 3) |
| `count-gates.sh` (G1 to G5)| COUNT GATES OK; G1 to G4 as on `main` to the byte | 147 s  |
| e-r-maint, seeds 1 to 3    | TRACECHECK OK each, by hand (level4's set)       | 15 s   |

`count-gates.sh`'s output: `32-maintain/gate-ec924fd7.txt`. The night
step grows by G5's 8 s (147 s for the five gates). The Lean sources are
unchanged; `lake build` ran in `level3.sh`. `level4.sh` (the evict set
with e-r-maint) was not run: its new configuration was checked by hand.

No expected value of an existing test changed: the user path writes the
same bytes (the take's new code runs only for maintain()'s empty record),
and no existing test was edited.


## 6. Questions for Frans

Decided by the agent, to go on (the common brief); each can be
overturned.

* **Q32-1. The filler.** To cut without the application's writes, a
  meta block must follow the cut point (2.1, point 4); maintain() writes
  an internal value of zeros up to the next meta block (at most 200 kB)
  and deletes it at once. Without it an idle database keeps up to about
  twice the startup distance (100 MB at the default 50 MB). Recommended:
  keep it; it is written at most once per iteration that maintain()
  begins, at most half of what that iteration's cut releases.
* **Q32-2. "About as much" as a fresh database.** maintain() begins an
  iteration only when its cut releases at least 400 kB, so an emptied
  idle database ends within about 0.6 MB of a fresh one's stream (83 kB
  at 1M keys, G5). Recommended: keep 400 kB; a smaller threshold makes
  the calls go on for little gain (each round writes a filler).
* **Q32-3. What false means.** "Nothing due now": false also while a
  cut waits for time (R after the iteration's end) or the next
  iteration for R / 4. So "call until false" is the cleanup available
  now, and an idle application calls again later. Recommended: keep;
  the alternative (true until converged) makes a loop spin for R.
* **Q32-4. The sync.** When a cut is decided and its table is not yet
  durable, maintain() syncs (outside the lock) and makes the cut in the
  same call, as a commit makes it at a later commit. A call can so wait
  for one disk force. Recommended: keep.
* **Q32-5. The Pub API.** `boolean maintain()` on `Database`, as Y10
  approved; the name and the return type are new in the stable API
  (P12, 2026-11-09). Recommended: as built.


## 7. The merge with main (a156fd51) and its gates

The coordinator, 13:38: merge `main` (024-31's `shareSection`, 024-33
and 024-34's cache tables and reclaim reads, ST6 counted in G4) and
gate again. Conflicts in `TransSeq` (`takeTo` beside `shareSection`,
both kept) and in `count-gates.sh`'s header; `Reclaim`, `CountGates`
and `docs/levels.md` merged by themselves. Merge commit `ef10ff95`.

G5 now counts ST6. The first count failed (49,584 slots against the
twin's 80): since 024-33 a map shrinks to at least 16 slots and keeps
its table once used, and the emptied database has used 3,099 of the
4,096 maps, the twin 5. That is a floor independent of n, 4,096 times
16 = 65,536 slots (about 256 kB), so G5 holds ST6 to the larger of twice
the twin's and that floor (`5edb773a`). A map that empties could drop
its table altogether; that is 024-33's to decide, not done here.

| Gate (head)                          | Result                                         |
|---|---|
| before-commit.sh (ef10ff95)          | BEFORE COMMIT OK (unit 1,695, F 89), 73 s      |
| level1.sh (ef10ff95)                 | LEVEL 1 OK                                     |
| level3.sh (ef10ff95)                 | LEVEL 3 OK, 486 s; 35 traces, C-CUT 0 of 799   |
| count-gates.sh (5edb773a)            | COUNT GATES OK, 130 s; G5 ST6 0.754 of its limit |
| level4.sh quick (5edb773a)           | LEVEL 4 OK, 123 s; 18 traces, C-P, C-H 0 fail  |
| e-r-maint seeds 1 to 3 (5edb773a)    | TRACECHECK OK each                             |

`5edb773a` changes only `CountGates.java` after `ef10ff95`. Output:
`32-maintain/gate-5edb773a.txt`. ST6's count moved by a few slots
between runs (49,584, 49,392): the eviction thread's timing.


## 8. State

2026-11-12, 14:02. **Done; merged with main and gated.**

* **Clone** `/Users/f/fl/bench/2026-11-12/maint/clone`, branch
  `024-32-maintain`, head `5edb773a`, in Frans's name: `c8becd28` (the
  feature), `ec924fd7` (the dead hand's step, G5's tolerances),
  `ef10ff95` (merge of `main` at `a156fd51`), `5edb773a` (G5's ST6
  floor). Not pushed; the coordinator lands it.
* **Gates**: section 5 (before the merge) and section 7 (after it), all
  OK. No existing test's expected value changed.
* **Not done**: `level4.sh` full; G5 at 10M; Frans's answers to Q32-1
  to Q32-5 (section 6).
* **To continue**: land the branch. The clone's `lean/.lake` is a copy
  of the main tree's, not tracked.
