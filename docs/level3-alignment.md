# BergDB Level 3: the Java code and the Lean model

By Claude (Opus 5.5, Claude Code) for Frans Lundberg, from 2026-10-16.
Work packages A2, R1 and later of bergdb item 001
([../items/001-lean-model-levels-3-4/01-plan.md](../items/001-lean-model-levels-3-4/01-plan.md)).
Source commit `a66e4d9` (R1); line numbers below are at that commit, in
`java/src/bergdb/`.

Status, 2026-10-17: R1's version, with R2's traces (2.7) and R3's model
(2.8). The scope (section 1), α for reclaim (section 2), the register
(section 3, checked against the code at `75d3c2d` in A2 and at `a66e4d9` in
R1), the arguments for M32 and M38 (section 4) and the safety argument in
the model's terms, every step marked (section 5). To come: R7 the red list
(section 6); R9 the outcome.

Level 3 is reclaim: the front of the stream is cut, so that the stream does
not grow forever. How Java does it is in [levels.md](levels.md), "Level 3:
reclaim", and in the class comment of `core/Reclaim.java`. The plan of item
001 aligns it with the model after the model has the cache (stage 2), since
reclaim's safety depends on what a written version names, which Level 4
decides (the plan, "How the levels depend on each other"). This document
says what "aligned" means for reclaim, as
[level2-alignment.md](level2-alignment.md) does for Level 2. The cache is in
[level4-alignment.md](level4-alignment.md).


## 1. Scope

* Reclaim's records: user transactions, reclaim steps and table stores, as
  records of the model; the touch; the first available time; cuts, decided
  and made.
* What makes a cut safe in the model (`CutOK`, the plan, 8.7), and the
  theorems T8, T9, T12 and T-SCHEME (the plan, 1.4, stage 3).
* Reads from the first available time on, and restarts from a cut stream.

Not in the model: when an iteration starts and how much a step rewrites
(the allowance; a policy, like the startup pos policy at Level 2); the
retain duration and the wall clock (the model gets f, not R); bytes,
durability and the order of file deletions
([level3-durability.md](level3-durability.md)); readers that expire while a
cut overtakes them (concurrency; decision D1 = A, levels.md, W1).


## 2. The mapping α for reclaim

Written in A2 as a draft from the plan's 8.1, completed in R1 (2026-10-16).
Times and records as in level2-alignment.md, 2.1: model time i is the time
of record R(i), and a Java lookup at time t is a lookup at the model time
max { i : tt(i) ≤ t }. Line numbers at `a66e4d9` (`core/Reclaim.java` and
`core/Db.java` are unchanged since `75d3c2d`).

### 2.1 Records

Every executed transaction is a record (`Db.executeInner`, 1349: `store()`,
1386, writes one record for each). With reclaim on, three kinds:

* **User transactions** (external): `Trans.isInternal()` false.
* **Reclaim steps**: internal transactions with `Trans.touch` set
  (`Reclaim.step`, 345; lines 431 to 439).
* **Table stores**: internal transactions without a touch that put the
  table (`Reclaim.storeTable`, 648).

Reclaim runs in `Reclaim.transactionCompleted` (262), which
`executeInner` calls at its end (line 1403), inside the write lock, after
the user transaction's record and `transExecuted`. It ignores internal
transactions (line 263), so reclaim does not nest. One call writes, in this
order, at most: a table store when an iteration starts (lines 271 to 280);
one step (282 to 288), followed by a table store if the step ended the
iteration (`step`, 472 to 485); a table store if a row became safe
(`markSafePositions`, 492, line 504); and a table store if a cut is decided
(`pretruncateIfPossible`, 574, line 612). The physical cut (`cutIfDurable`,
309, at line 292) writes no record. So between two user transactions the
model sees zero to five internal records, in that order, each an ordinary
transaction of the model: its own time (`dbClock.transactionBegin`), its own
startup pos and taking of D (`store`, 1407), its own entries.

A step that throws a `RerunException` writes no record (4.2).

### 2.2 T(i) and touch(i)

* **T(i) of a user transaction**: as at Level 2 (level2-alignment.md, 2.7).
* **T(i) of a step**: its value nodes with their keys: the rewrites, one
  `put(key, value)` for each key that the step's scan finds live at tStart
  and whose value at the step's own read time is stored before pCut (line
  393: `value != null && gd.tpos < it.pCut`), with the same bytes; and the
  current row, under `/#i/dreclaim/-current.txt`, a value computed by a
  value transformation during the transaction (lines 416 to 423) from the
  step's progress and the index bytes the step has made dirty
  (`Trans.dirtiedBytes`).
  The value transformation runs inside `putKvs` before that put
  (`kv.transformValue`); for the model it is just the value put. A rewrite
  is a new data node (a data node has one version), so after the step the
  key's value is the same bytes in a node created at the step's record.
* **T(i) of a table store**: one put, the serialized table under
  `/#i/dreclaim/-table.txt` (`storeTable`, 648; M37).
* **touch(i)**, for a step only: the index nodes that `Db.touchRange`
  (1570) visits for the key range (touchFrom, touchTo], touchFrom excluded,
  touchTo included, null for the first or last key (`Trans.touchFrom`,
  `touchTo`, set at lines 438 and 439 from the row's lastKey and the last key
  of the step's scan): every index node that a `GetMany` at the
  transaction's own time follows over the range through the writer's
  pointer follower, and the super root (`superRootAccessed`). `putKvs` runs
  the touch before the puts (1530 to 1538) and makes the visited nodes dirty
  at once (`endOfOp(true)`, 868; `makeDirtyIfNeeded`, 900), whether or not
  anything changes; `endOfTrans` (879) does not remove replaced nodes from
  D for a touch transaction. So touch(i) is computed on P@(i-1) at time i,
  and step 3 of record i marks touch(i) besides the access paths of T(i)
  (M17). The touch makes no entries.

The ranges of an iteration's steps cover every key: the first step starts
at lastKey = null, each next step after the last key of the one before, and
the last step (the scan's end of data) ends at null.

### 2.3 Iterations: positions and times

An iteration is a row of the table (`IterationInfo`): pStart, tStart, pCut,
lastKey, done, tEnd, pEnd, pSafe, cut. Each position is at a record
boundary and maps to the record that starts there; each time maps to a
model time.

* **pStart, tStart**: when an iteration starts, in the call after user
  record R(u): pStart = the stream length after R(u) (`t.nextPos`, line 267),
  so the record that starts there is the table store that follows; tStart =
  tt(u) (lines 275 and 276). The row is stored at once (line 279).
* **pCut**: the pStart of the previous iteration; the first iteration's own
  pStart (line 277). So c(it) is the record that starts at the previous
  iteration's pStart.
* **The scan** of every step is at tStart (line 353): it lists the keys live
  at model time u. The values are read at the latest time (lines 379 to
  384; the step's read time `t.readTime`, line 429).
* **tEnd, pEnd**: the time and the start position of the iteration's last
  step, R(e) (lines 481 and 482). The table store right after R(e) stores
  done, tEnd and pEnd (line 484).
* **pSafe**: in a later call, after user record R(v), when the current
  startup pos has reached pEnd: the stream length after R(v) (lines 492 to
  505). It maps to the record after R(v).
* **cut**: true once a cut is decided at the row (2.5).

The start condition (twice the startup distance of stream growth and a
quarter of the retain duration since the last start, no iteration in
progress, retention finite), the allowance of each step (lines 283 to 287)
and the size of a step are policy: they decide when the records come, not
what they are, and are not in the model (section 1).

### 2.4 fa(i), the first available time

`Reclaim.firstAvailableLookupTime` (141) changes only when a cut is decided
(line 621, after the table store of line 612) and when the database starts
(`initFromDb`, 516, lines 542 to 562): in both cases it is the tEnd of the
newest row marked cut in the table, 0 if none. So, as a function of the
records: **fa(i) is the model time of tEnd of the newest row marked cut in
the table as stored at or before R(i); 0 before the first cut** (Q5). It
never decreases (a cut needs `row.pCut > firstAvailablePos`, line 593, and
the newest cut row has the largest pStart) and is below the time of the
startup pos (2.5, condition 2). `firstAvailablePos` is the cut row's pCut:
c, as a position.

### 2.5 Cuts: decided, then made

A cut is decided in the call after user record R(u), at time tt(u), at the
newest row (largest pStart) that meets all of (lines 586 to 594):

1. done, and tEnd older than the retain duration: tt(u) - R > tEnd;
2. pSafe set and passed: the current startup pos (after the records of the
   call so far) at or after pSafe, so also after pEnd and pCut;
3. the last valid meta block names a transaction at pCut or later (line 591;
   recovery starts there);
4. pCut after the current firstAvailablePos (cuts move forward).

If that row is not yet cut, the rows that started before it are removed,
the row is marked cut, and the table is stored: record R(d), the decision
(lines 605 to 612). Then fa = tEnd and firstAvailablePos = pCut (621, 622).
In the model: **the cut decided at R(d) is at c = the record that starts at
the row's pCut, with f = fa(d) = the model time of tEnd.**

The physical cut comes later: `cutIfDurable` (309) calls `pretruncate(pCut)`
when the stream is durable up to its length right after R(d) (line 626).
`FileStream.pretruncate` deletes whole files below pCut, so the stream's
first position moves to the start of the file that holds pCut, at or below
it; `MemoryStream` keeps whole 1 MB arrays; `CutStream`, a test stream,
refuses every read below the exact position (M35). The model's cut is the
decided c: Java can still read some bytes below c, never bytes the model
keeps that Java lost.

### 2.6 Reads, and what is not in the model

* A read at a time before fa is refused at admission
  (`LookupTimeNotAvailableException`; `Db.getOneInternal`, 1068, lines 1073
  to 1080; `getMany`, 1116, lines 1131 to 1138). The model requires reads
  from f on only (M36).
* A read admitted before a cut can reach bytes the physical cut then
  removes; it expires (`Db.expiredIfReadBelowCut`, 1170) if its actual
  lookup time is now before fa. Concurrency, outside the model (decision
  D1 = A; levels.md, W1); measured by `ReclaimReaders` and the Level 3 soak (WP
  P2).
* Not in the model: the wall clock and the retain duration (condition 1 is
  a policy that chooses f), the meta block condition (3: bytes and
  recovery, [level3-durability.md](level3-durability.md)), durability and
  file deletion, the allowance and the iteration spacing.

### 2.7 For the trace (R2)

What a format-2 trace of a reclaim run needs per record, from the above:
the kind (user, step, table store); for a step, its touched nodes, as ids
(TOUCH lines); the record's fa (FA, only when it changes: at a decision R(d)
and after a restart); for a decision R(d), the cut row's pCut as the record
c that starts there (CUT); and, at the record after which `cutIfDurable`
made it, the physical first position (PHYSCUT). Positions as record
numbers, times as model times.

**Done in R2** (2026-10-17). `java/stress/TraceExport.java` with `retain=S`
(reclaim on, the clock scaled as `RestartInvariance`'s, the stream a
`CutStream`, which refuses every read below the cut) writes these lines
(level2-alignment.md, 9.2). Every executed transaction is a record: run A
records each through test-only hooks in `Db` (`Db.TestHooks`: after every
executed transaction, for every value node created, for every node a touch
visits; null by default, and nothing then changes), so reclaim's steps and
table stores get their own `TX` blocks. The cuts come from the table
(`Reclaim.lastCutRow`, a test accessor): fa(i) as in 2.4, a `CUT` when a new
row is marked cut. Run B restarts every ten transactions and right after
each call that decided a cut, checks D and lookups from the first available
time on, and compares the streams from the cut. The exporter's own checks:
every touched node is an index node of P; every stored position (each
reference, startup pos, top pos and first touch) is the start of a version;
the physical cut is at or below the decided one (M35); Java's first
available time is the table's. `java/stress/reclaimtraces.sh` writes the
plan's sets (8.4): **small**, five configurations of five seeds (node sizes
8 and 14, 30 to 200 keys, 300 to 800 user transactions, deletes 0 and 25
percent, long keys, transactions that change nothing): 25 traces, 3 to 28
cuts decided each, no exporter error, no failing probe; **medium**, three
configurations of two seeds (2,000 to 5,000 user transactions): 6 traces, 18
to 46 cuts each, no error, no failing probe. The physical cuts depend on
when the stream is durable (`cutIfDurable`), which a background sync
decides, so their number varies from run to run; the records do not.
References to versions before a cut decided earlier are common (Option K
names the latest version of every pointee, dead ones too; a cut stream keeps
their stubs, plan 8.7): 10 to 107,000 per trace. The checker reads these
lines from R7 on.

### 2.8 In the model (R3)

**Done in R3** (2026-10-17). The Lean model has Level 3's definitions
(lean/README.md, "Changes to the trusted part", WP R3):

* **touch(i)** is `Changes.touch`, part of the changes of T(i) (a function
  of T(i), i and P@(i-1), as the rest; the plan said `Spec.touch`). Step 3
  adds the touched index nodes not in D that it did not find otherwise
  (`touchOf`, `gotDirty3`), and the writer's paths reach them (`pathOf`).
  Java's touch marks the touched nodes first and then the access paths of
  the puts (2.2); the model's gd lists them in another order, which the
  checker does not compare (gd as a set). The plan's TouchOK is three fields
  of `StepOK`: the touched nodes are index nodes reachable at i-1, and every
  node reachable then with a touched node below it is touched too, but a
  virtual root. Java's traversal walks down from the super root through
  live pointers (2.2); with TREE every reachable node's reachable ancestors
  are on that walk. **T13'** (`T13_markTouch`) is proved: step 3, by testing
  or by marking, gives exactly the index nodes not in D that are dirty or
  touched. Every earlier theorem holds with touches; the proofs needed the
  transitive `touchUp` (a clean node above a touched one would otherwise be
  outside D with a pointee in D), that a root child that a root child points
  to is not reachable (`VInv.deadTops`, from `VirtStep.dead`; so the super
  root of a touch is the newest one), and A6' at the time before the change
  as well as after it.
* **fa(i)** is `Record.fa`, from a policy (`Algo.faPolicy`) clamped so that
  it never decreases and stays at most s(i) (`firstAvail`). Java's (2.4) is
  such a policy.
* **The cut** keeps, for the records before c, stubs of their versions
  (node, record number, level, kind) and drops their histories, references,
  transactions and gd lists (`Version.stub`, `Record.cut`, `cutStream`).
* **CutOK** (`SIS/Reclaim.lean`), the plan's sketch with part 3 refined,
  and f the first available time of the last record:
  1. c ≤ f = fa(k) (and f ≤ s by `firstAvail`);
  2. every version that a read at some time from f to k may follow is at c
     or later: a lookup's (`ReadsAt`: the latest versions of the nodes
     reachable then, and the versions their pointers to live children lead
     to, with Rule R) and, since R6, a physical read's in the running process
     (`ReadsPhys`: through a pointer to a live child also every version of
     the child at or after the record it names). R3 asked this of the latest
     versions only, refined in R7 and R6, below;
  3. every node in D has its latest version at c or later, or none, and
     every reference below c of that version names the latest version of
     its node (so a node not in D);
  4. top(k) names a record at c or later (implied by 2).
  R7 found (`staleWitness` in SIS/ReclaimExample.lean) a run where R3's part
  2 holds and a physical read at f, after a restart from the cut stream,
  reads a stub: a tree root that is reachable at f and replaced later names
  an older version of a child, before the cut, while the child's latest
  version is after it; the model's startup still gets P right there (it takes
  each node from the read at the latest time it is reached), its physical
  reads do not. With part 2 on every version a lookup from f on may read,
  the cut there is ruled out. In the random runs of `reclaimtest` the two
  give the same cuts. R4 found (`cutReadWitness`, 2.9) a run where R7's part
  2 holds and a read in the running process with eviction, whose Rule R is
  that of an earlier startup, follows a replaced node's pointer to a version
  before the cut; since R6 (register M48, option (a), Frans), part 2 covers
  the versions that such reads may follow (`ReadsPhys`), and the checker's
  C-CUT checks it (R4's diagnostic C-CUT+ is part of it; test trace
  `physcut.trace`). But not through a version that Rule A put back and that
  is still in D: the running memory reads that node through its canonical
  object, which D pins (R6, part 1b, `schemeWitness`: without the exception
  Java's scheme does not give part 2, while its reads are right).
  The sketch's part 3 asked only that no reference below c name a node in
  D. A stale reference below c to a node not in D is as bad for Java: it
  cannot read the target's id below the cut, so it can neither link the
  slot to an object of D nor apply Rule R to it (M33), and the model's
  startup reaches a node of D that is no longer reachable only through such
  references (M41). The refined part 3 is the pSafe wait: a parent written
  before its child and kept in D by Rule A must be written again
  (`pSafeWitness` in SIS/ReclaimExample.lean is a run where only part 3
  rules out a cut).
* **Lookups from f on** (`SameFrom`): every node but a virtual root has the
  same content at every time from f to k, and a virtual root the same live
  children. A startup from a cut stream rebuilds the virtual root from the
  root children it can read, so the root's entries for older ones are gone
  (the first random runs found this; Java's TopDs after such a restart holds
  only the top nodes it can read too). T12 then needs a transaction to see a
  virtual root only through its live children (`ExecRootOK`; BergDB's
  transactions start at the current super root).
* **Runs** that restart from cut streams: `runRestartsCut` (logical) and
  `runEvictCut` (with eviction and cache schedules); `PolicyCutOK` asks
  that the policies give the same startup pos and first available time on a
  stream cut at or before its first available time.

Checked by running (SIS/ReclaimExample.lean, `lake exe reclaimtest 20 30`):
example 4, F1-008-07's reclaim example adapted to BergDB (a virtual root
with top nodes and root splits, reclaim steps that touch and rewrite the
values stored before pCut, f at the end of an iteration once the startup pos
has passed it), on random runs that restart at random from the stream cut at
the largest c with CutOK: for four startup pos policies and 20 seeds of 30
transactions, the assumptions (the touch's included) and PolicyCutOK hold,
T8 holds at every restart (startup from the cut stream gives the same
lookups from f on and the same D) and T12 for the run (the stream is the
run's, cut at the largest cut; the same D; the same lookups from f on); with
eviction and the four cache schedules, 9,600 transactions, each followed by
the records and D, reads from f on (also on the cut stream from the running
memory, as T9 will say), the invariants, and the restarts from the cut
streams: none fails. 125 of the cuts had a node in D that is not reachable
from f on (the delicate case of the plan's 8.7, M34): the startup from the
cut stream rebuilt it right in every one. Without CutOK's part 2, T8 fails at
once; without part 3 or 4, nothing fails in the model, which links a slot to
D by node id even below the cut (M33 is Java's limit, part 3 is for Java).
On a fixed run (`#guard`): without the touch, no cut is safe, since an empty
leaf keeps its only version in R(0).

### 2.9 Recovery and reads after a cut (R4)

**T8 is proved** (`T8_recoverCut`, 2026-10-17): after a safe cut at c in the
state after T(k), startup from the cut stream gives the same lookups at every
time from f to k (`SameFrom`) and the same D. Its reads for the times from f
to s read no record before c, only versions that `CutOK`'s part 2 covers
(Rule R uses the startup section, which a cut at or before s leaves whole);
what its reads for earlier times find of the cut records (stubs) matters only
before f; and D comes from the records after s. With a virtual root, startup
rebuilds the root from the root children it can read; those live from f on
(created at or after the one live at f) are read at their latest versions,
which part 2 covers, so the rebuilt root has the root's live children from f
on (`VirtLiveOK`), and the section's transactions, which see the root only
through its live children (`ExecRootOK`), make the same changes. P up to s
agrees with P after T(s) for lookups from f to s, and the rerun keeps that to
k. Both assumptions hold for example 4 (proved), and for BergDB by its
super root (TopDs).

**T9 is stopped** (the plan's stop rule 4). Physical reads from f on in the
running process can read a record before a cut that `CutOK` allows.
`cutReadWitness` (SIS/ReclaimExample.lean) is such a run of the model, with
eviction (after each transaction every object that may be evicted is) and no
restart since R(0): the tree root 20, reachable at f = 2 and replaced at 3,
names mid node 2's version of R(0); the mid node's latest version is of R(6),
in the startup section after T(6), so lookups' reads (`ReadsAt`) take that
one by Rule R, and `CutOK` allows a cut at 1. The running memory's Rule R is
that of its last startup, which does not know the version of R(6), and the
mid node's canonical object was evicted; so the read at 2 follows the tree
root's slot to R(0), which the cut removed, and gives the mid node without
its entries. Without eviction the same read gives P (schedule 0): the mid
node keeps its canonical object. In general, without eviction, a node without
a canonical object has no version after the last startup (the writer makes
every node it writes canonical, and nothing is released), so a read loads the
version that `ReadsAt` names or the node's latest version, which part 2
covers (argued, not proved). Java today evicts nothing (M26); with eviction
(stage 4, J6) it could (register M48).

What T9 needed was Frans's decision (M48; decided: (a), below):

* (a) `CutOK`'s part 2 over every version that a physical read from f on may
  follow: through a pointer to a live child, every version of the child at or
  after the one the pointer names (Rule R of any earlier startup, and objects
  newer than the pointer, give only those). Java's scheme gives it: every
  index node reachable at tEnd was touched by the iteration and written
  after its touch, so the pointers that reads from tEnd on follow name
  versions written after pStart, and pCut ≤ pStart; R6 would prove it with
  the rest of T-SCHEME. Java's cuts meet it: the checker's diagnostic C-CUT+
  finds no version before the cut that a physical read from f on may follow
  at any of the 288 cuts of the small set, nor at the 47 of the medium set's
  two mixed traces (its four largest were still in the checker at R4's
  commit). In the random runs of example 4 it lowers the largest safe cut
  in 28 of 1,600 states. Then T9 is to prove for the Level 4 memory, with an
  invariant on the slots (the record a slot names, after the last startup's
  Rule R, is at or after the one that the latest version of the slot's node
  names), which T12 with eviction (R5) needs too.
* (b) The window (M44's fallback): Rule R in the running process also over
  the records written since the last startup; a change of the physical
  layer, in the model and in Java (stage 4).
* (c) T9 only for reads after a restart from the cut stream. Weaker: Java
  cuts while it runs.

Recommendation: (a). It changes no code, Java's scheme gives it, and it is
what Java's reads in the running process will rely on after a cut once
objects can be evicted.

**Decided: (a)** (Frans, 2026-10-17 14:07). `CutOK`'s part 2 becomes the
stronger one; R6 proves that Java's scheme gives it, then T9 is proved for
the Level 4 memory with the invariant on the slots.

**Done, the definition** (R6, part 1, 2026-10-17): `ReadsPhys` and `CutOK`'s
part 2 over it (lean/README.md, "Changes to the trusted part", WP R6). T8 is
proved as before (`ReadsAt.phys`). In example 4, `cutReadWitness`'s cut at 1
is no longer safe, and the checker's C-CUT includes the old C-CUT+ (test
trace `physcut.trace`). R6's proof that Java's scheme gives it, and T9, are
next.

**Refined** (R6, part 1b, 2026-10-17). T-SCHEME, tried by running before
proving it (example 4's random runs with the scheme's conditions: the touches
cover, the rewrites, the startup pos past tEnd and then past that point,
j0), failed in 1 of 22,832 states with the wait for tEnd not strict, and in
none with Java's strict waits (222,857 states, and 161,731 more with erratic
startup pos policies); a search for the pattern behind the failure gave a
witness with the strict waits too (`schemeWitness`). During the
settling a stale chain of versions that Rule A put back forms: the tree root,
put back while its mid node is in D, names the mid node's version of R(6),
itself put back while a leaf was in D and naming the leaf's version of R(0).
At the decision (startup pos 8, past j0 = 7) the tree root is still in D with
that version, so part 2 over every pointer reaches R(0), before the cut at 1.
Java's running memory, and the model's with every cache schedule, read the
tree root through its canonical object, which names the mid node's latest
version, and get P on the cut stream. So `ReadsPhys` does not extend through a
version that Rule A put back and that is still in D (its node's canonical
object is pinned, and no snapshot of the version exists); through it, only
what lookups read. With this exception the scheme gives part 2 in every state
checked, also with the waits not strict (444,220 states: 100 runs of 100
transactions for each of 8 startup pos policies; and 166,150 of 60 runs of
80; and the witness); a second wait (past the point where the startup pos
passed j0) also cures the witness, without the exception. The decision for Frans, if he
prefers otherwise: this refinement (done; recommended, since it changes
nothing in Java and follows what the running memory reads) or that wait in
Java's reclaim.

By running (scratch probes, not kept): example 4's random runs, with the
four cache schedules and restarts every few transactions or none, reads at
every time from f on, on the stream cut at the largest safe c, from the
running memory, after every transaction: 27,040 transactions, and 3,600
runs aimed at a state where the stronger part 2 is lower; no failure.
Example 4's reclaim writes every node reachable at f after the cut point, so
its pointers are fresh; the witness needs an empty subtree (spec4e: keys 2
and 3 have no values yet at f) and a fixed f.


## 3. The register

Checked against the code at `75d3c2d` in A2, and again at `a66e4d9` in R1,
2026-10-16 (line numbers at `a66e4d9`). Columns as in level2-alignment.md,
section 6. Status: open (o), resolved in a WP (WP name), closed (c). M17 is
reopened from level2-alignment.md.

| | Mismatch or open question | Java | Model | Proposed resolution | Stage, WP, status |
|---|---|---|---|---|---|
| M17 | Reclaim's touch marks nodes without adding entries: every index node the range traversal follows, and the super root, get dirty; the marks stay when the transaction replaces a node | `Db.touchRange` (1570); `endOfOp(true)` (868) in `putKvs` (1521), lines 1530 to 1538; `endOfTrans` (879) skips touch transactions | step 3 (`markOf`) | Model: `Changes.touch`, TouchOK in `StepOK`, T13' (α: 2.2). R7: Java's `endOfTrans` keeps every mark of a touch transaction, so the nodes that the step's puts mark and replace stay in D, which the model does not mark (red list, section 6): a Java change, R8 | 3: R3 (2.8: done, T13' proved); R7 (red list); R8 (done: `Db.endOfTrans`, 2026-10-17); c |
| M32 | Java keeps the first available time in the reclaim table, a value in the database, and reads it after startup (Codex's review of 09, finding 5): `Db.startInner` calls `DbStarter.start` (through `startDb`) and then `reclaim.initFromDb` (line 511), which reads the table through the reconstructed database | `Reclaim.initFromDb` (516); `Db.startInner` (486), line 511; `Reclaim.pretruncateIfPossible` (574) | — | Model: fa(i) in records, by α (2.4, Q5); argued in 4.1 that Java's startup needs f only after reconstruction, if it reads nothing before c (T8, R4) | 3: R1 (argued), R3 (`Record.fa`, 2.8), R4; o |
| M33 | After a cut, Java cannot read the id of a slot's target below the cut: a stored key node holds child positions, not ids, so the id is read from the target's header, and `resolvePointers` skips a stream slot below the stream's first position (Codex's review of 09, finding 2) | `NodeCollection.resolvePointers` (317), line 337; `StoredKeyNode.toLongs` (50) | `javaTest` (by id) | Model: version stubs keep positions; CutOK must imply that no such slot of a node in D names a node in D; otherwise a code change (5, step 7) | 3: R3 (CutOK part 3: every reference below c of a node in D names its node's latest version, 2.8), R5; o |
| M34 | Java writes every taken node, also nodes that no lookup from f on reaches (F1-008-08's "needed" nodes) | `Db.store` (1407); `TransSeq.take` (83) | step 6 | Model: show that it changes no record after a safe cut (T12), or a needed test in code (5, step 7) | 3: R5; o |
| M35 | A cut is decided (in the table, with the first available time and position) before it is made (when the stream is durable past the table); `FileStream` deletes whole files, `MemoryStream` whole 1 MB arrays; `CutStream` (a test stream) refuses reads below the exact cut | `Reclaim.pretruncateIfPossible` (574), `cutIfDurable` (309); `stream/FileStream.pretruncate` (262); `storage/BufferedStream.pretruncate` (446); `stream/CutStream.read` (60) | `cutStream` | α: the model's cut is the decided position; the physical cut comes later, at the same or a lower position (2.5) | 3: R1 (α); R2 (the exporter checks it on every trace: no failure in 31, 2.7) |
| M36 | Reads before f are refused (`LookupTimeNotAvailableException`), and an admitted read may expire when a cut overtakes it (D1 = A): a `ReadBelowFirstPosException` below the cut becomes an expiry if the read's actual time is now before f | `Db.getOneInternal` (1068), lines 1073 to 1080; `Db.getMany` (1116), lines 1131 to 1138; `Db.expiredIfReadBelowCut` (1170) | `view` (every time) | Model: reads required from f on; expiry is concurrency, outside the model (2.6) | 3: R3 (`SameFrom`, 2.8), R4; o |
| M37 | Reclaim stores its table and the current row as values under internal keys (`/#i/dreclaim/-table.txt`, `/#i/dreclaim/-current.txt`), in internal transactions; the row's value is computed by a value transformation during the step | `Reclaim.storeTable` (648); `Reclaim.step` (345), lines 416 to 423 | T(i) | α: ordinary puts; T(i) is what the record stores (2.2) | 3: R1 (α); R2 (the traces have them as ordinary entries, 2.7); the checker from R3 on |
| M38 | A reclaim step can fail with a `RerunException` (a conflict with its read time) and then writes no record; the step is tried again at a later transaction. A table store cannot fail so (`Bug`) | `Reclaim.step` (345), line 449; `storeTable` (648), line 657; `Db.stmCheckConflicts` (1474), called at line 1362 | — | α: no transaction; nothing to model (argued in 4.2; the exception cannot occur today) | 3: R1 (argued) |
| M41 | After a restart from a cut stream, startup reads D's nodes at their newest section versions or stored positions, and the root chain from topPos | `DbStarter.canonicalNode` (455), `topNodeOfLastTransaction` (293), `findSuperNodeAtStartupTime` (263) | `startup` | CutOK must cover them. For the root chain, review-13-claude, 4.3: a search at a time q loads, besides its answer, only tops created at or after q; so from tEnd on, the tops created after tEnd and the top live at tEnd (5, steps 4 and 6) | 3: R3 (CutOK parts 3 and 4, 2.8), R4 (T8: the model's startup), R5; o |
| M48 | **New (R4).** Java cuts while it runs, and reads after the cut go through the objects and slots made before it, with Rule R of the last startup. With eviction, a read at a time from f on can follow the slot of a node that a later change replaced to a version before the cut: the last startup's Rule R does not know the pointee's newer version, and the pointee's canonical object was released. Today nothing is released (M26), so such a pointee has its canonical object | `NodeCollection.followStreamPointer` (184; Rule R from `DbStarter`'s maps); `Reclaim` cuts while the database runs (2.5) | `CutOK` part 2 (`ReadsAt`, Rule R of the current section); `Mem.follow4` (Rule R of the last startup) | `cutReadWitness` (SIS/ReclaimExample.lean): `CutOK` holds, a read at f in the running process fails on the cut stream (2.9). For Frans: (a) part 2 over every version a physical read may follow (every version of a pointee at or after the one the pointer names); Java's scheme gives it, Java's cuts meet it (C-CUT+); (b) the window (M44); (c) T9 after restarts only. Recommended: (a). **Decided: (a)** (Frans, 2026-10-17) | 3, 4: R4 (found; T9 stopped, stop rule 4), Frans ((a), 2026-10-17), R6 (stronger part 2: the definition done, 2026-10-17, refined for versions that Rule A put back, `schemeWitness`, 2.9; Java's scheme gives it: to prove), then T9; o |

Findings of A2: none beyond the plan's list for Level 3. Noted for R1: the
touch marks the super root of the step's time (through
`superRootAccessed`), which review-13-claude's argument about the root chain
after a cut (M41) uses. Findings of R1: none that needs a new row. Two
notes: the conflict check that M38 is about cannot fail today (4.2); and
`pSafe` is the stream length after the user record of the call that sets it,
which is before that call's own internal records (2.3), so it is a little
earlier than "the stream length when the startup pos passed pEnd" of
levels.md, which the argument in section 5 allows (step 5).


## 4. The arguments

### 4.1 M32: Java's startup needs f only after it has reconstructed the database

The model's startup reads the last record's fa first and reconstructs P
for the times from f on. Java's `Db.startInner` (486) reconstructs first
(`DbStarter.start`, through `startDb`, line 506), and reads f afterwards
from the table (`reclaim.initFromDb`, line 511). The two agree if Java's
reconstruction neither uses f nor reads anything that the cut removed.

1. **Nothing in the reconstruction uses f.** `DbStarter` finds the meta
   blocks and the startup section, reruns the section, and resolves the
   root chain and D; none of it reads `Reclaim` (which has fa = 0 until
   `initFromDb`). After `initFromDb`, f is used only by the admission of
   reads (2.6) and by the next cut decision (condition 4 of 2.5).
2. **What the reconstruction reads.** (a) The meta blocks and the startup
   section, from the startup pos of the last record to the end of the
   stream (`Db.startInner`: `nodeStream.recover`, line 493, and
   `readTransactions`, line 502; `DbStarter.doOrdinaryStartup`, 121). (b) The
   root chain: the top node that the last record names (topPos;
   `topNodeOfLastTransaction`, 293) and the search for the super root at
   the startup time (`findSuperNodeAtStartupTime`, 263). (c) The rerun of
   the section's transactions (`rerunTransactions`, 344), which follows the
   paths of their keys at their own times, all at or after the startup
   time. (d) D's nodes: the canonical object, the newest version in the
   section, or the version at the position stored with the got-dirty id
   (`canonicalNode`, 455). Then (e) `initFromDb` reads the table and the
   current row at the latest time.
3. **None of it is before c, given a safe cut.** (a) is after c: the
   decision needed the startup pos at pSafe or later (2.5, condition 2), and
   the startup pos never decreases. (b), (c) and (e) read versions of nodes
   at times at or after the startup time, which is after f (the record of
   pEnd is before the startup pos): CutOK's parts 2 and 4 (section 5) say
   that these versions are at c or later. (d) is CutOK's part 3.
4. So, with CutOK, Java's startup from the cut stream is the model's
   startup from the cut stream with f supplied after the reconstruction,
   and the order does not matter. That is T8 (`T8_recoverCut`, proved in WP
   R4, 2.9) for Java's startup, with M41 (the root chain and D) as its
   Java-specific part.

Marks: step 1 checked (code, above); step 2 checked (code); step 3: for the
model's startup proved (T8, R4), that Java's cuts are safe to prove (R6); it
is also tested, since every test with `CutStream` refuses a
read below the cut, and `ReclaimStress`, `RestartInvariance` with reclaim and
`level3.sh` restart after cuts.

One more place reads before `initFromDb` sets f: a read by another thread
while `start()` runs would pass admission with fa = 0. `start()` has not
returned then; the API does not offer reads before it returns.

### 4.2 M38: a step that throws a RerunException is no transaction

`Db.executeInner` checks conflicts (`stmCheckConflicts`, 1474, called at
line 1362) under the write lock and before `dbClock.transactionBegin`
(1365), `putKvs` and `store`: the exception leaves no record, uses no time,
and changes no node. `Reclaim.step` returns at once (line 449) and has not
changed the row (`it.set(next)` is at line 470), so the next call repeats
the step from the same lastKey. The model sees no transaction: nothing to
model.

The check cannot fail today. A step reads its keys (`b.keyRead`) at
`stepLookupTime`, the latest time when its reads begin (lines 379 to 384),
and executes inside the same hold of the write lock that ran the user
transaction (`transactionCompleted` is called at line 1403): no transaction
runs between the reads and the check, so no key was modified after the read
time. A table store reads nothing; `storeTable` treats the exception as a
`Bug` (line 658).

### 4.3 M35 and M37: by α

Both are settled by the mapping (2.5 and 2.2); R2's traces check them
(CUT and PHYSCUT lines; the table and the row as ordinary puts).


## 5. What makes a cut safe

The argument of levels.md ("Level 3: reclaim") in the model's terms, for a
cut decided at R(d) for the iteration `it` (2.5): c is the record at
it.pCut and f the model time of it.tEnd, the last step R(e). Each step is
marked **proved** (with the theorem), **to prove** (with the WP),
**checked** (with the code or test) or **assumed**. "CutOK c f" is R3's
(2.8), the plan's sketch (8.7) with part 3 refined:

1. c ≤ the record of f ≤ s, the startup pos;
2. every version that a read at some time from f on may follow is at c or
   later: a lookup's (`ReadsAt`), the latest versions of the nodes reachable
   then and the versions their pointers to live children lead to (with Rule
   R), and since R6 a physical read's (`ReadsPhys`), also every version of a
   live child at or after the record that the pointer names;
3. every node in D has its latest version at c or later, or none, and every
   reference below c of that version names the latest version of its node
   (so no node of D: M33);
4. top(k) is at c or later (implied by 2).

The steps:

1. **Order: c ≤ rec(f) ≤ s.** pCut is the previous iteration's pStart (or
   its own), before the iteration's records; R(e) is a step of the
   iteration; the decision needs the startup pos at pSafe ≥ (the record
   after) pEnd. **Checked** (code: 2.3 and 2.5); R3's `CutOK` states it.
2. **Values live from f on are at c or later.** A key live at a time t ≥ f
   has a data node created at the key's last put before t. If its last user
   put before t came after tStart, that record is after pStart, so after c.
   Otherwise the key was live at tStart with no user put up to t, so the
   step whose range holds it (at a time before tEnd ≤ t) found it in its
   scan, read the same data node, and rewrote it if that node was stored
   before pCut: a new data node at that step, after c. In every case the
   data node live at t is at c or later. **To prove** (R6, T-SCHEME), from the
   coverage of the ranges (2.2) and the rewrite rule (line 393); **checked**
   by `Reclaim.Tester.testIterationRewritesAllOldValues` and
   `testLookupsFromFirstAvailableTime`, and by every `CutStream` test.
3. **Index nodes reachable from f on get an entry or a mark after c.**
   Every index node that is current at the time of the step whose range
   meets its key range is in that step's touch(i) (2.2), and every index
   node created later is new. A key range only shrinks when a node splits,
   so an index node reachable at a time t ≥ f either existed at the step
   time of every range it meets and was touched, or was created after that.
   Deleted-only nodes and the segment subtrees of deleted long keys are
   visited by the range traversal too (bug 3 of levels.md). **To prove**
   (R6, from `Changes.touch` and TouchOK of R3, with the coverage of the
   ranges and TREE); the B-tree's key ranges are Java's, not the model's: R6
   states the coverage as an assumption on the touch (as F1-008-07, section
   8, "Reclaim coverage"). R2's traces record each step's touch (TOUCH lines),
   but checking the coverage needs each node's key range, which neither the
   trace nor the model has: a check on the Java side (each node reachable at
   the step's time whose key range meets the step's range is in its TOUCH
   line) is left to R6.
4. **The root chain.** The super root at each step's time is touched
   (`superRootAccessed`); a search at a time q ≥ f loads, besides its
   answer, only tops created at or after q (review-13-claude, 4.3), and its
   answer is the top live at q, which is the super root at some step time,
   or the top live at tEnd, or created after tEnd. **To prove** (R6, with
   M41; part 4 of CutOK).
5. **Every touched or new node is written after its mark.** A node marked
   (dirty) in record j is taken and written once the startup pos passes j
   (the take rule: step 6 of the model; `TransSeq.take`). The decision
   needs the startup pos at pSafe, after pEnd, after every step of the
   iteration; so every node of steps 3 and 4 has a version at c or later,
   and so does every node created after it (CutOK part 2 for index nodes).
   The take rule is the model's step 6 (a definition), and Java's take is
   **checked** against it by the Level 2 conformance (level2-alignment.md,
   section 13); the combination with steps 2 to 4 is **to prove** (R6).
6. **References after pSafe.** A parent written after its touch, before
   a child of D was written, names the child's version before the cut; Rule
   A then keeps the parent in D (it points to a node of D), so it is
   written again after the child. pSafe is the stream length after the user
   record of the call in which the startup pos passed pEnd (2.3): every node
   of D at that moment got dirty before pSafe, so it is written once the
   startup pos passes pSafe, now naming its children's versions after c.
   This gives CutOK part 3's first half for the nodes reachable from f on,
   and part 4 for the root children. **To prove** (R6); no test needs the
   wait for pSafe (levels.md, "Evidence"); it is kept from this argument.
7. **Nodes in D that no read from f on reaches.** Rule A can keep an
   historical node in D (a node no longer current, with a child in D); it
   is not reachable from f on, and steps 3 to 6 say nothing about it. Its
   slots may name versions before c (M33), and Java writes it when it is
   taken (M34). CutOK part 3 asks that its latest version be at c or later
   and that every reference of it below c name the latest version of its
   node, so a node not in D, one that no read from f on reaches either (by
   part 2). R3's random runs met such nodes at 125 cuts, and the startup
   from the cut stream rebuilt each right (2.8). **To prove** (R5, T12: such nodes either are written again
   after c, or their writes change no record after a safe cut), or a code
   change (R8). This is the delicate case of the plan's 8.7.
8. **The time condition: tEnd older than R.** A policy that chooses f; the
   model allows any f with CutOK. **Assumed** (outside the model); the
   retention guarantee (lookups in [now - R, now] work) is **checked** by
   `ReclaimRetentionTester`, `ReclaimStress` and the soak.
9. **The meta block condition and durability.** Recovery starts at the
   transaction that the last valid meta block names, so that must be at c
   or later (condition 3 of 2.5), and the cut waits until the table that
   marks it is durable. Bytes and recovery, outside the model. **Checked**
   (f-test `testCutKeepsMetaBlockTransaction`; level3-durability.md).
10. **Reads after the cut, and restarts across cuts.** With CutOK: startup
    from the cut stream gives the same lookups from f on and the same D (T8,
    **proved** in R4, 2.9; 4.1 for Java's order); physical reads from f on in
    the running process need more once objects can be evicted (T9,
    **stopped** in R4: `cutReadWitness`, M48; Frans chose (a), so **to
    prove** after R6); and a run with restarts and
    cuts writes the same records as the run without them (T12, R5). Java:
    **checked** by `RestartInvariance` with reclaim (the same stream byte
    for byte, with and without restarts), `ReclaimStress`, `CrashTest` with
    reclaim, `level3.sh`, and the soak's checks after cold restarts
    (WP P2).

What is left to prove, in short: steps 2 to 4 and 6 (R6, T-SCHEME: Java's
scheme gives CutOK), step 7 (R5, or a change in R8), and step 10 (T9 after
R6's stronger part 2 (M48: (a)); T12, R5).
What is assumed: the policies of steps 8 and 9, and that a step's range
traversal visits every node whose key range meets the range (step 3), which
R6 takes as an assumption on the touch, and checks on Java (R2's traces
record the touches, 2.7).


## 6. Red list

**R7** (2026-10-17). The checker with R3's definitions (lean/README.md, the
checker; bergdb item 001, WP R7): C-A checks TouchOK for every TOUCH line;
C-S compares fa(i) too (FA lines, Java's value clamped by the model's
`firstAvail`) and, from the first CUT on, runs the model's step on the stream
cut at the largest cut so far (version stubs before it); C-CUT checks
`CutOK` at every CUT line, in the model's state after its transaction, that
the CUT's first available time is the record's, and that every PHYSCUT is at
or below the decided cut (M35). Run on R2's reclaim traces (2.7): small, 25
traces, 14,448 transactions, 288 cuts; medium, 2 of its 6 traces (rm-mixed-1
and rm-mixed-2: 4,415 transactions, 47 cuts); its four largest (rm-5000-1 and
2, rm-long-1 and 2) were still in the checker at R7's commit.

| Failure | Where | Row | Smallest | Resolution |
|---|---|---|---|---|
| C-S, gd and D: in a reclaim step, Java's gd(i) has nodes that the model's has not: index nodes on the access path of the step's puts (the current row's value, outside the step's range) that the puts replace (a split), so not reachable after the step, and not touched. The model marks the touched nodes (`touchOf`, kept if replaced, as Java keeps them) and the access path of the change after it (`markOf`); Java's `endOfTrans` keeps every mark of a touch transaction (`if (!x.trans.touch && ...)`, Db.java 892; d5c56dd: "reclaim's touch transactions keep every mark"), the put paths' too | 29 transactions of 11 small traces; 43 transactions of 2 medium traces | M17 | r-del-4, T(189): nodes 1300 and 41514, which the step's put replaces by 224726 and 224724 | R8, a Java change: in a touch transaction, `endOfTrans` takes out of D the replaced nodes that the puts marked, and keeps those the touch marked (the touch's marks are the first `gotDirtyNodes`, made by `endOfOp(true)` after `touchRange`). Then Java's gd(i) is the model's. The other way, a model change (step 3 of a transaction with a touch also marks the put paths' replaced nodes), would add to the model what the Level 2 alignment took out of Java (d5c56dd, M2); and the replaced nodes are dead: writing them later serves no read |

Nothing else fails: no C-A failure (TouchOK holds for every touch: the
touched nodes are index nodes reachable before the change, and every node
reachable then above a touched one is touched, but the virtual root), no
fa(i) difference, no C-S failure on the cut streams beyond the row above, no
C-CUT failure (CutOK holds at every cut Java decided, with the first
available time of the record, and every physical cut at or below the decided
one), no failing probe of run B (C-R), no C-L failure, and no diagnostic (D
closed upward, A6, TREE, A-COPY). The Java tier: `level3.sh`'s reclaim checks
(ReclaimStress, RestartInvariance with reclaim, CrashTest with reclaim,
ReclaimReaders) passed in P3's gates (2026-10-17 06:13 to 06:33, `8ea39cb`),
and `java/` has not changed since.

**R8** (2026-10-17): the row's change is made (`Db.endOfTrans`; test
`DbTester.testTouchTransactionReplacedNodes`, failing before it). On R2's
small reclaim set made again with it: 25 of 25 traces TRACECHECK OK (14,448 transactions, 288 cuts; C-CUT and C-CUT+ without a failure), C-S without a failure; the red
list is empty. Only runs with reclaim have other records (StreamDigest
against `l34-base`: the 24 digests of the Level 2 configurations are the
same, byte for byte; 10 of the 12 of the Level 3 ones differ).

So every failure maps to a register row (M17), and R8 has one more Java
change. The summary per trace: `docs/evidence/level3-redlist-baseline.txt`.
