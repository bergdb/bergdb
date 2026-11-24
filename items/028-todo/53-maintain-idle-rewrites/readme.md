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
of section 8, recommendation the simplest A (8.6); Frans approves before
anything of A lands (17:13). No option changes what `maintain()`
promises; A changes the stream's bytes and what a start reads, B makes
the rewriting reach more databases, and C keeps a released bug open
(034-01, no release with a known bug).

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
after it. Puts alone leave one set (`RowsProbe 100000 5000000 20`, and
028-51's runs after the puts): the calls are quiet. 028-51's rule
neither causes the rewriting nor stops it (028-51, section 3).

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
next one's": `Db.maintain()`'s calls "begin iterations and do their
steps by the clock, without that growth. So they help a database that
the application no longer writes to"; "Called again and again, with
time passing, it brings a database that has been emptied to within about
400 kB of the stream of a fresh one"; "A call when nothing is due writes
nothing". The Pub's `Database.maintain()` says the same of an emptied
database, and that "Each call's work is small and bounded".

The rewriting of sections 1 and 2 breaks none of these: each cut
releases 400 kB or more (the old copies), each call's work is bounded,
and no sentence says that the calls go quiet in a database with live
values. It is a cost, writes and wear for no space (about 2.5 MB an R at
30,000 values of 100 bytes; 010-01, P3 and P4, principles, not
promises), not a released bug (033's rules leave out performance).

RB-007 breaks the emptied database's promise and "So they help a
database that the application no longer writes to": registered in 033,
S4 (disk space only; the commits' rule gives the space back after 2 sd
of writes), in 2026.5 and 2026.6. It is RB-006's condition with the
writes before the cut instead of after it.

### 5. Why no fix here, and the options

Both faults need what M1 does not know: where the application wrote.
From the stream's positions alone, a rule either counts reclaim's own
rewrites, and goes on rewriting (the first rule; the rules from the
last pStart and from pSafe that 028-51 tried and dropped), or misses the
application's writes (the second rule, for those before the store).
Two other ways were dropped: an estimate of the live bytes in a stretch
from the rows' `rewritten`, which counts as live the copies that the
application then deleted, so an emptied database would keep its stream;
and a scan of the live values' positions, not bounded in one call, and
not the same after a restart if spread over calls (INV-RESTART).

The options, A (a mark of the application's writes kept with reclaim's
table), B (M1's second rule counted from the last pStart, one line) and
C (no change), are in section 8, with A in full.

### 6. A first prototype of A

`prototype-a.diff`, on `48178c65`, not landed: W in memory only (a start
set it to 0), M1 as in section 8.1. The same quiet runs as section 8.3;
`HoleProbe 4000 20000` kept 21,616 bytes, `20000 20000` 196,560. Section
8's prototype, with W kept in the stream, replaces it.

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

### 8. Option A in full, its cost, and the options

Written 2026-11-24 by an agent of lead-1124, after Frans's direction of
17:13 (log). The prototype: the branch `028-53-a` of the clone `c53a`,
on `72326123`, and `prototype-a2.diff` here; not landed.

#### 8.1. The design

* **W**: the position of the newest record of the application's, or -1:
  a record with a value or delete node and none at a key under
  `/#i/dreclaim/` (005-42's test, `ConnectionImp.isReclaims`). Reclaim's
  steps, table stores, settings and fillers all hold such a key; M4's
  transaction holds no KV. In memory: `Reclaim.recordWritten`.
* **In the stream**: a name `w` in the last row of the table's text
  (027-03, section 15), at most 15 bytes, at every store of the table.
  Canonical: -1 if W is before the first row's pCut, as no rule compares
  it with such a position. A row without `w` (2026.6, `main`) gives W =
  the store's position; 2026.6 ignores `w` and drops it at its next
  store.
* **The store when the startup pos passes the table**: with q the
  position of the table's last store, after a user transaction's work, a
  `maintain()` call or a settings change, if sp > q, the table is stored
  again. So between calls a start's section holds every record after q.
* **A start**: W := the last row's `w`, then the newest record of the
  application's after q in the section, if any; if sp > q (a crash
  between a record and that store), W := sp, as if the application
  wrote after q.
* **M1** (027-13, section 1.10), conditions as now:
  * W >= fp, the application wrote in the stream kept: 028-51's two
    rules, or (c) W >= lastPStart and the stream from lastPStart is at
    least 400 kB (RB-007's writes);
  * W < fp, only BergDB wrote in it: only if the last iteration rewrote
    at most X = 100 kB, and the stream from fp to lastPStart, or from
    lastPStart, is at least 400 kB.

  So a database not written to is quiet from the cut of the second
  iteration that began after W; an emptied one drains reclaim's own
  records; one written to begins iterations by the clock, as now.

#### 8.2. Its complexity

* **Code**: about 80 lines in `Reclaim` and `Db`; about 150 lines of
  tests: `HoleProbe`'s and `IdleLiveProbe 15000 1000000 20 10`'s cases
  (both fail on `main`), the same W and bytes over restarts
  (`probes/ProtoA.java`), a row without `w`, a start with sp > q. Texts:
  027-03, section 15; 027-13, sections 1.1, 1.2, 1.9, 1.10; the Javadoc
  of `Db.maintain()`, `Database.maintain()`, `MAINTAIN_MIN_RELEASE`.
* **State**: one number in the table's last row, one more moment when
  the table is stored (no format version); W and q in memory.
* **A start**: four cases (no table; a row without `w`; sp <= q;
  sp > q). Recovery: none new (a torn record is gone before reclaim
  reads). One new invariant: between calls, sp <= q.
* **Proofs and checkers**: nothing to learn. The model leaves out the
  table, when an iteration begins and `maintain()` (027-13, section 5;
  030-25); the new stores are records of kind `table`, which the trace
  checker takes as any; steps and rows are as now.
* **Bytes**: every stream with a finite retain duration; two unit tests
  that pin a store or a stream call need new numbers (8.3).

#### 8.3. Measured

The prototype, `main` in brackets:

* RB-007: `HoleProbe 4000 20000` keeps 176,736 bytes, the twin 315,024
  (4,804,384 and 315,008); `20000 20000` 177,344 and 199,376 (5,361,912
  and 872,424).
* `IdleLiveProbe`, the last 10 R: nothing in every run: 30,000 values at
  sd 1 MB after 10 rounds (24,522 kB), 15,000 (14,554 kB), 100,000 at
  sd 1 and 5 MB (51,595 and 55,421 kB), and where `main` is quiet too,
  small databases (0 to 2,000 values) among them.
* `ProtoA SD EVERY`: the same W after every operation and the same
  bytes, sd 5 kB to 1 MB, a restart every 7 to 101 operations (2,919
  restarts at 7).
* StreamDigest quick: l2 as `main`, l3 not (16 of 44 lines); the four
  modes agree in each.
* Gates on the branch (with K, 8.4): `BEFORE COMMIT OK (88 s)`; COUNT
  GATES OK (G5: kept 174,176 bytes, `main` 80,600); the conformance's
  reclaim and crash sets, CONFORMANCE OK (40 and 15 traces). Without K
  two unit tests fail: `Reclaim.Tester.testRestartResumesIteration`
  (adjusted on the branch) and `StorageFaultTester.testStopWhileReading`.

#### 8.4. The simplest A, and what each part buys

* **W kept and found again** (the field, the store, the start's scan):
  every A needs it. Without the store a start cannot see the writes
  after the table's last store, and the stream would depend on restarts
  (P2).
* **Rule (c)**: counts RB-007's writes.
* **The rule for W < fp**, about 10 lines: stops the rewriting and
  drains reclaim's own records. W and (c) alone (`-Dproto53.min=true`)
  keep 921,504 bytes in `HoleProbe 4000 20000`, over 400 kB more than a
  fresh database, and rewrite as `main`: it is part of the least A that
  fixes RB-007.
* **K**, not in 8.1, about 15 lines (the prototype: 1 MB): the table is
  stored again only once the stream has also grown by K since q, and a
  start reads the records from q to sp. It bounds the stores where sd
  is below K (StreamDigest's l3 streams, sd 500 to 10,000 bytes: -0.6 %
  to +0.3 % with K, +20 % to +63 % without, a store after most
  transactions), at the price of a read beyond the section, which the
  bound on startup (027-11) would have to cover. Without it the table is
  stored at most once per sd of writes: a table of 30 rows, a few kB,
  is under 1 % of the writes at sd 1 MB.

#### 8.5. The options weighed

* **The simplest A** (8.1): fixes RB-007 and the rewriting. Writes: `w`
  at each store of the table and a store per sd. Format: a name in the
  row. Complexity: 8.2. Risk: a fault in W changes when iterations
  begin, not what a read returns (steps and cuts as now); ProtoA and
  StreamDigest check W byte for byte over restarts.
* **A with K**: the same, fewer stores below sd 1 MB; 15 lines more and
  a read beyond the section.
* **B**: fixes RB-007 in one line; no state, no format change, low risk.
  Writes: every database with live values that is not written to
  rewrites them under the calls, about once each R/4 to R/2, as long as
  the calls go on (3,066 kB in 10 R at 3,000 values, where `main` and A
  write nothing; measured on `48178c65`).
* **C**: nothing. RB-007 stays a released bug (a release needs Frans's
  exception, 034-01); the rewriting stays (24.5 MB in 10 R at 30,000
  values).

#### 8.6. Recommendation

The simplest A. Weighed for simplicity (010-01, P11 and P13): B is the
simplest fix of the bug, but it makes the rewriting, writes and wear for
no space (P3, P4), the rule for every quiet database that calls
`maintain()`, the use `maintain()` is for. A adds one stored number, one
store rule, one start rule and one branch of M1, which no proof or
checker has to learn, and its stream over restarts is checked byte for
byte. K is left out: it saves stores only below sd 1 MB. B if Frans
judges A too complex for 2026.7: it fixes RB-007, and the rewriting
stays a known cost.

State, 2026-11-24, 17:30: in progress, for Frans's choice of section 8
(recommended: the simplest A). The Done when is met but for the fix.
Nothing of A has landed; its prototype is on the branch `028-53-a` of
the clone `c53a` (`prototype-a2.diff`). With A or B: the change, the
tests of section 8.2 (failing on `main`), RB-007's fix in 033, the notes
and next.md, and the gates of the Done when (for A also StreamDigest and
the conformance's reclaim and crash sets).


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

2026-11-24, 16:47. Taken again by an agent of lead-1124 (clone c53a,
branches 028-53 and 028-53-a): option A in full as a design, with a
prototype that keeps W in the stream.

2026-11-24, 17:13. Frans, through the lead: A is a big change with
tradeoffs to make; it must not get too complex, and he approves before
anything of it lands. The design to measure A's complexity, find its
simplest version and weigh simplicity (010-01, P11 and P13).

2026-11-24. Option A designed in full (section 8), its prototype built
and measured on the branch 028-53-a (f03744b9): RB-007 and the rewriting
fixed, the same stream over restarts. Recommendation: the simplest A
(without K); B if A is judged too complex. Status in progress for
Frans's decision.
