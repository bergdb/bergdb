028-53. Investigate: maintain() keeps rewriting live data in an idle database
==============================================================================

Status: in progress. Kind: Investigate. Frans: decision.
Created 2026-11-24 by Frans Lundberg.

What: on `main` before 028-51, an idle database with about 4.5 MB of live
data or more, which has had reclaim iterations begun by commits, keeps
rewriting that data under regular `maintain()` calls: 24.5 MB written per
10 R with no user writes. Found by 028-51 while it compared rules for
`maintain()`'s M1 (its probes, `IdleLiveProbe`); 028-51's rule writes
exactly what `main` wrote in every idle run, so it neither causes nor
fixes this.

Why: `maintain()` on a quiet database should cost little once the stream
holds nothing to give back; rewriting the same live values again and
again costs writes and wear for no space (010-01, P3 and P4). Whether it
breaks what `maintain()`'s Javadoc promises decides whether it is a
released bug (033's rules, Frans 2026-11-24).

Frans: none, unless a fix changes what `maintain()` promises (then
options in the entry). Since 2026-11-24: a decision between the options
of section 5 below, recommendation A. No option changes what
`maintain()` promises; A changes the stream's bytes and what a start
reads, B makes the rewriting reach more databases, and C keeps a
released bug open (034-01, no release with a known bug).

Done when: the case reproduced on `main` (028-51's probe or a new one),
its cause in `Reclaim` named, the Javadoc of `Db.maintain()`,
`Database.maintain()` and `Db.setRetainDuration()` read against it; if it
breaks a promise, an RB entry in 033; a fix with a test that fails before
it, or the reason it stays, written here; `java/before-commit.sh` prints
`BEFORE COMMIT OK`, with the reclaim conformance, CountGates and
StreamDigest as the change needs.

First step: 028-51's readme and its probe `IdleLiveProbe`, and 027-13,
sections 1.10 and 6.


Result
------

Investigated 2026-11-24 by an agent of lead-1124, on the branch `028-53`
of a clone of `main` at `48178c65`. The probes: 028-51's `IdleLiveProbe`
([../51-maintain-m1-written-db/probes/](../51-maintain-m1-written-db/probes/)),
and this entry's `probes/RowsProbe.java` (the table's rows at each
change) and `probes/HoleProbe.java` (writes while an iteration waits for
its cut). MemoryStream, a test clock, R = 1 s, one `maintain()` call a
millisecond; counts and sizes only, no times.

### 1. The case reproduced

`IdleLiveProbe LIVE SD 20 10`: LIVE keys of 100 bytes put, 10 rounds of
overwrites, then 20 R of calls and no writes. Written in the last 10 R:

* `main` and release 2026.6, the same bytes in every run: 30,000 keys at
  sd 1 MB, 24,522 kB (46,941 kB in the 20 R; the stream kept 9,989 kB;
  the last call that returned true 19,500 of 20,000); 15,000 keys,
  14,554 kB; 100,000 keys, 51,595 kB; 100,000 keys at sd 5 MB,
  55,421 kB; 30,000 keys at sd 5 MB nothing, quiet from call 2,620.
* Release 2026.5: 30,000 keys at sd 1 MB, 22,303 kB.

### 2. The cause in Reclaim

M1's first rule, in `Reclaim.maintainBeginDue` (027-13, section 1.10):
an iteration begins if the stream from fp to the last pStart is at
least MIN_RELEASE (400 kB). After the cut of iteration k, fp is its
pCut, the pStart of iteration k-1, so that stretch holds what k-1
wrote: its rewrites. Iteration k+1's pCut is k's pStart, so k+1 rewrites
the live values stored before it, the copies that k-1 made, and none
of those that k made; its cut releases the copies that k-1 replaced. In
a database not written to, the live values so fall into two sets that
the iterations rewrite in turn, each cut releasing the old copies of
the set it rewrote, and the stream kept stays as it is. It goes on
while both sets' iterations write 400 kB or more.

`RowsProbe 30000 1000000 20 10` shows it: after the overwrites, rows
that rewrote 3,478 kB and 2,008 to 2,024 kB in turn; stretches between
pStarts of 3,846 to 3,887 kB and 2,166 to 2,267 kB in turn; an
iteration about every 1,300 calls (1.3 R: its steps, then R until its
cut, and the next begins at once); the stream kept about 10 MB.

The two sets come from the writes: the live values stored before the
pStart of the last iteration that a commit began, and those stored
after it (in the run above, the rounds' last writes before and after
64,952 kB). Puts alone left, in `RowsProbe 100000 5000000 20`, only
the first iteration, whose pCut is its pStart: after its cut the first
rule's stretch is empty, and the calls were quiet (nothing in the last
10 R); so were 028-51's runs after the puts (3,000 to 300,000 keys).
028-51's rule neither causes the rewriting nor stops it: it counts the
stream after the table's last store, which is empty in a database not
written to (028-51, section 3).

### 3. Found with it: RB-007

The application's writes made after the last pStart and before the
table's last store, while the last iteration ran or waited for its cut,
are counted by neither rule: the first counts the stretch before the
last pStart, and the second the stream after the store. They come into
the first rule's stretch only when another iteration has begun. So
after the cut of an iteration that began within 400 kB of its cut point
(the first, whose pCut is its pStart, or one that began R/4 after an
iteration with nothing to cut: RB-006's condition), no iteration
begins, and those writes stay for good below 2 sd, the commits' rule of
growth.

`HoleProbe 4000 20000`: 4,000 keys put and deleted, calls until the
first iteration is done, 20,000 keys put and deleted before its cut,
then 10 R of calls. `main` keeps 4,804,384 bytes, the twin without the
second writes 315,008, and no call writes or returns true after call
621; release 2026.6 the same; release 2026.5 5,087,688 against 546,824.
`HoleProbe 20000 20000` on `main`: 5,361,912 against 872,424.

### 4. What maintain() promises

The Javadoc of release 2026.6, as on `main` but for 028-51's "or the
next one's" (2026.5's `Db.maintain()`: "calls of this method bring it
back without them", and an emptied database "to about the stream of a
fresh one"):

* `Db.maintain()`: "Calls of this method begin iterations and do their
  steps by the clock, without that growth. So they help a database that
  the application no longer writes to, and one that it writes to slowly
  after deleting much"; "Called again and again, with time passing, it
  brings a database that has been emptied to within about 400 kB of the
  stream of a fresh one, as an iteration begins only if its cut would
  release at least 400 kB"; "A call when nothing is due writes
  nothing"; its return: "False if nothing is due until time passes (a
  quarter of the retain duration for the next iteration, the retain
  duration for a cut) or the application writes".
* The Pub's `Database.maintain()`: "An application that has deleted much
  and then writes little or nothing can call this method, now and then,
  to have the space back without writes of its own. Called again and
  again, as time passes, it brings a database that has been emptied to
  within about 400 kB of the size of a fresh one"; "Each call's work is
  small and bounded".
* `Db.setRetainDuration()`: "maintain() begins iterations by the clock,
  without commits (bergdb 026-13, U13-4)"; the Pub's
  `Database.setRetainDuration()`: "A database that is not written to
  does none of this by itself; maintain() lets the application ask for
  it (bergdb 024-32)".

The rewriting of sections 1 and 2 breaks none of these: each iteration's
cut releases 400 kB or more (the old copies), each call's work is
bounded, a call writes only when the rule makes an iteration due, and
no sentence says that the calls go quiet in a database with live values
that is not written to. It is a cost, writes and wear for no space,
about 2.5 MB an R at 30,000 values of 100 bytes, against 010-01's P3 and
P4, which are principles, not promises. Not a released bug: 033's rules
leave out performance.

RB-007 (section 3) breaks "it brings a database that has been emptied to
within about 400 kB of the stream of a fresh one" (`Db.maintain()`; the
Pub's the same) and "So they help a database that the application no
longer writes to": registered in 033 as RB-007, S4 (disk space only;
nothing lost or wrong; the commits' rule gives the space back after
2 sd of writes), in 2026.5 and 2026.6, not fixed. It is RB-006's
condition with the writes before the cut instead of after it; 028-51's
fix counts only those after it.

### 5. Why no fix here, and the options

Both faults need what M1 does not know: where the application wrote.
From the stream's positions alone, a rule either counts reclaim's own
rewrites, and goes on rewriting (the first rule; the rules from the
last pStart and from pSafe that 028-51 tried and dropped), or misses the
application's writes (the second rule, for those before the store).
Two other ways were considered and dropped:

* An estimate of the live bytes in a stretch from the rows' `rewritten`
  (the iteration before the last one's, from the table stored at the
  last pStart): after the application deletes values that an iteration
  rewrote, `rewritten` counts the dead copies as live, and the calls
  would keep an emptied database's stream, the promise that RB-007
  breaks; and reclaim's own records add about 10 % to an iteration's
  stretch beyond `rewritten` (388 kB of 3,866 kB above), a margin that
  passes 400 kB at stretches of about 4 MB.
* A scan of the live values' positions at M1's decision: a walk of
  every key in one call (not bounded), or, spread over calls, a decision
  at other calls after a restart (INV-RESTART, 027-13, section 3).

**Option A, a mark of the application's writes kept with reclaim's
table (recommended).**

* W, the stream length after the application's last transaction that
  wrote a KV: in memory, set in `Reclaim.transactionCompleted`.
* Kept in the stream: a field `w` in the row's text (027-03, section 15),
  W at the store, in every row that reclaim stores (the table, the
  current row). A start takes W from the latest stored row, then moves it
  to the end of each later record it reads that is not one of BergDB's
  own (by its keys). So that the start finds them: reclaim stores the
  table, in a small internal transaction, when the startup pos has
  passed its last store and the application has written since (at most
  once a startup distance of the application's writes), and the start
  reads from the earlier of the startup pos and that store (at most one
  record's take more than now). This part is the design still to
  settle and test: a crash between an application's record and that
  store, and the takes of `maintain()`'s M4, which move the startup pos
  too.
* M1, with its conditions as now (no iteration runs, R/4 since the last
  began, no cut pending):
  * if W is after fp (the application wrote in the stream kept): the
    first rule, the second (028-51), or a third, for RB-007: W after the
    last pStart and the stream from the last pStart at least 400 kB;
  * otherwise (only BergDB wrote in the stream kept): an iteration
    begins only if the last one rewrote at most X (100 kB in the
    prototype: a database emptied, or nearly), and the stream from fp to
    the last pStart, or from the last pStart, is at least 400 kB. An
    emptied database so drains its own records and fillers; one with
    live values is quiet.
* Effect: a database not written to is quiet from the cut of the second
  iteration that began after the application's last write; RB-007's
  writes are given back; a database written to goes on beginning
  iterations by the clock, as now.
* Cost: about 15 bytes a row; the extra store; the start's longer read
  in that case. Every stream with a finite retain duration changes its
  bytes (StreamDigest's reclaim configurations, 018-01, section 2).
  027-03, section 15, and 027-13, sections 1.1, 1.2, 1.9 and 1.10; the
  Javadoc's description of M1 (`Db.maintain()`, `Database.maintain()`,
  `MAINTAIN_MIN_RELEASE`). What `maintain()` promises stays; it holds
  again. Tests: sections 1 and 3's cases (both fail on `main`); the same
  stream over a restart in a database with live values; the present
  ones. About a day.

**Option B, the second rule counted from the last pStart, no new
state.** M1's second rule counts the stream from the last pStart, not
from the table's last store. RB-007's writes are after the last pStart,
so it is fixed, in a line, and the promises hold. But every database
with live values not written to then rewrites them under the calls,
from a few thousand values on. Measured on `48178c65` with that line
changed (not landed): `HoleProbe 4000 20000` kept 21,616 bytes and
`HoleProbe 20000 20000` 196,560, as with A; `IdleLiveProbe` wrote, in
the last 10 R, 3,066 kB at 3,000 keys at sd 5 MB after the puts and
3,087 kB at 3,000 keys at sd 1 MB after the rounds, where `main` and A
write nothing (028-51 measured 3.1 MB for the first), and 24,522 kB at
30,000 keys at sd 1 MB, as `main`.

**Option C, no change for now.** The rewriting stays a cost. RB-007
stays open, so a release needs Frans's exception (034-01).

Recommendation: A, as its rule is measured (section 6) and makes both
cases right; the field, the store and the start's reading are the day's
work. B if a release is due before A is done: it fixes the bug, at the
cost of more rewriting.

### 6. A prototype of A

`prototype-a.diff`, on `48178c65`, not landed: W in memory only (a start
sets 0), X = 100 kB, M1 as in A.

* `IdleLiveProbe`: nothing written in the last 10 R in every run: 30,000
  keys at sd 1 MB (6,298 kB in the 20 R, the last call returning true
  3,634, kept 6,112 kB); 15,000 keys (3,278 kB; 3,353); 100,000 keys at
  sd 1 MB (20,844 kB; 5,592) and at sd 5 MB (25,678 kB; 5,759); 3,000 and
  8,000 keys at sd 1 MB after the rounds; 3,000 and 5,000 keys at sd
  5 MB after the puts.
* `HoleProbe 4000 20000`: kept 21,616 bytes, the twin 315,008, no work
  after call 3,858. `HoleProbe 20000 20000`: 196,560, the twin 199,384
  (872,424 on `main`).
* The unit tests of `Reclaim` and its testers (49) pass,
  `ReclaimMaintainTester` among them (`testSameStreamOverARestart` with
  W lost at each start: its database is emptied, where W does not change
  the calls); `count-gates.sh g5`: COUNT GATES OK, kept 80,600 bytes and
  the last call true 3,006 of 20,000, as on `main`.

### 7. What this entry changed

* 033: RB-007 registered (S4; not fixed), its counts.
* The section "After the release" of 2026.6's notes (a bullet) and of
  2026.5's (a pointer bullet); `releases/next.md`: RB-007 under the
  known released bugs, and RB-006's bullet no longer says that the calls
  "stay quiet" in a database not written to, which holds for 028-51's
  rule only.
* 027-13, sections 1.10 and 9: the first rule's rewriting and RB-007's
  stretch, as the code is.
* No change to `java/`: `java/before-commit.sh` on the clone, `BEFORE
  COMMIT OK (63 s)`.

State, 2026-11-24: in progress. The Done when is met but for the fix,
which waits for the choice of section 5. With A or B: the change, the
tests of sections 1 and 3 (failing on `main`), RB-007's fix in 033, the
notes and next.md, and the gates of the Done when (StreamDigest for A).


Log
---

2026-11-24. Registered by lead-1124, from 028-51's report.

2026-11-24, 13:40. Taken by an agent of lead-1124 (clone c53, branch
028-53).

2026-11-24. Investigated by the same agent: the rewriting reproduced on
`main`, 2026.6 and 2026.5 and its cause named (M1's first rule; the live
values rewritten in two sets in turn); not a released bug. RB-007 found
and registered (S4): the writes made before the cut of an iteration
that began within 400 kB of its cut point, counted by neither rule.
Options A, B and C for the fix, recommendation A, with a prototype's
measurements; status in progress for the decision.
