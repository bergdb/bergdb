028-47. Investigate: commits give a mass delete's space back by the clock
========================================================================

Status: open. Kind: Investigate. Frans: decision.
Created 2026-11-24 by Frans Lundberg.

What: 026-13's option B (U13-4, Q1), not studied in 2026.6: a commit
begins a reclaim iteration also on `maintain()`'s rule (a quarter of R,
a cut that releases 400 kB), so that `maintain()` is optional in effect
for a slowly written database. Option A, the Javadoc, was 028-06.

Why: after a mass delete followed by slow writes, the space comes back
many R later unless the application calls `maintain()`: in 026-13's C2,
6.4 MB kept at 10 R by commits alone, 1.2 MB at 2 R with `maintain()`
after each commit; in the Pub API, at its startup distance of 5 to
1,000 MB, after about 20 to 200 MB of new puts. Frans decided on
2026-11-13 that B is studied with G4 and taken only for a clear gain
(KISS); on 2026-11-24 that it is registered here, so that it is not lost
when 026 is done.

Frans: decision, after the study: B taken or not, the options in full
with a recommendation.

Done when: a report in this entry with G4 measured at C2's settings (a
startup distance of 1 MB, R = 200 drive transactions) and at the Pub
API's default, before and after B, in a clone; what B changes in the
stream's bytes of a slowly written database (not the format) and in
reclaim's proofs and checks (027-13, 030); a recommendation. No change
lands without Frans.

First step: read 026-13, section 6 and its C2 run, 027-13's pacing of
reclaim and `maintain()`, and 028-06.


Result
------

Study done 2026-11-24 by an agent of lead-1124, in a clone of `main` at
5f8395e7 (release 2026.6 and after). Counts and sizes only, no times.
Nothing of it is on `main`; the code of the options is on two branches of
the clone, for the lead to keep:

* **Option B**, as registered: branch `028-47-b`, commit da71233b. In
  `Reclaim.transactionCompleted` a commit begins an iteration when no
  iteration runs, R is finite, a quarter of R has passed since the last
  began, and either the stream has grown by more than 2 sd since then (as
  now) or `maintain()`'s rule of release holds (M1: no done iteration
  waits for its cut, and the new iteration's cut releases at least
  `MAINTAIN_MIN_RELEASE`, 400 kB). The rule is one method,
  `Reclaim.releaseDue`, that M1 and the commit share. 17 lines; code
  and comments only.
* **Option B2**, tried here because B gave no clear gain (section 3):
  branch `028-47-b2`, commit cbe46106, on top of B. A commit also does
  `maintain()`'s take (M4) when a done iteration's end is older than R
  and its cut waits for the startup pos: an empty internal transaction
  whose take goes on to that position (`Reclaim.clockTakeTarget`).

The probes are in `probes/`: `SlowDriveProbe` prints reclaim's table and
the startup pos during C2's workload; `TwinDriveProbe` prints the bytes
written by writer during G4's drive. G4 is `CountGates g4`
(`java/stress/count-gates.sh g4` with the properties below), C2 is
`java/stress/apps/c2-slow-drive/SlowDrive.java` against each build's
release jar.

### 1. G4 before and after

G4's workload: n = 1M keys put in key order and deleted, 100 a
transaction, then a drive of overwrites of one key of 1,000 bytes, beside
a twin with the drive only; the lag is the first drive transaction from
which kept stays at most twice the twin's M1 (026-11). R in drive
transactions; kept in MB.

* **G4's own settings** (sd 100 kB, R = 1,000, 40 R): every G4 line is
  the same in the three builds: lag 1,281 (1.28 R), M1 2.44 MB against
  the twin's 2.40 MB. Here 2 sd of growth (about 180 transactions) come
  before R/4 (250), so B's added rule never decides, and B2's take
  changes nothing there either.
* **C2's settings** (`g4sd=1000000 dt=50000`: sd 1 MB, R = 200, 40 R):

  | Build | Lag | Lag / R | First cut | Kept at 4 R | M1, twin's M1 |
  |---|---|---|---|---|---|
  | main | 2,969 | 14.8 | 1,848 | 197.6 | 5.79, 4.75 |
  | B    | 1,770 | 8.9  | 1,747 | 141.8 | 4.39, 5.73 |
  | B2   | 472   | 2.4  | 202   | 0.67  | 2.11, 2.55 |

  The lag gate (2 R) fails in all three. The gate ST6 (cache table slots)
  fails in all three too, 2.40 to 2.47 times the twin's (62,912 against
  25,488 on `main`): G4's gates hold at G4's settings; at C2's this one
  does not, before any change.
* **The Pub API's default startup distance** (`g4sd=50000000
  g4drive=500000`: sd 50 MB, R = 1,000, 500 R): the twin itself keeps
  hundreds of MB, so the lag, measured against twice the twin's M1, is 1
  on `main` and B and says nothing (2,042 with B2, whose twin keeps 32
  MB); kept at 4 R and the stream written say more. The twin's stream
  is its drive's bytes, in MB.

  | Build | Kept at 4 R | First cut | M1, twin's M1 | Twin's stream |
  |---|---|---|---|---|
  | main | 270.0 | 60,314 | 287.0, 279.3 | 779   |
  | B    | 244.5 | 75,573 | 221.3, 260.4 | 847   |
  | B2   | 3.42  | 1,002  | 3.59, 32.1   | 3,372 |

### 2. C2 before and after

C2 SlowDrive (026-13): a MemoryStream, 30,000 keys put and deleted, then
overwrites of one key of 900 bytes every 5 ms, R = 200 transactions, sd
1 MB, 40 R, beside a twin with the drive only. Kept in MB at 2, 4 and 10
R, its range from 20 to 40 R, the twin's range then, and the stream that
the drive wrote:

| Build, mode | 2 R | 4 R | 10 R | 20-40 R | Twin, 20-40 R | Drive wrote |
|---|---|---|---|---|---|---|
| main, commits    | 6.1 | 6.6  | 6.0 | 4.0-5.8  | 2.3-5.9  | 12.0 |
| B, commits       | 5.5 | 6.0  | 5.1 | 4.1-5.8  | 2.2-6.1  | 12.6 |
| B2, commits      | 3.3 | 0.63 | 1.9 | 0.78-2.6 | 0.71-2.6 | 8.7  |
| main, maintain() | 1.2 | 0.68 | 1.9 | 0.63-2.7 | 0.55-2.5 | 9.0  |
| B, maintain()    | 3.4 | 0.64 | 1.9 | 0.59-2.5 | 0.55-2.5 | 8.8  |

("maintain()": calls until false after each commit, on both databases.)
B gives C2 little: 5.1 MB at 10 R against 6.0, and the same range from
20 R on. B2 gives about what `maintain()` gives, one R later.

### 3. Why B does not help: the cut waits for the startup pos

`SlowDriveProbe` at C2's settings shows what holds the cut back (027-13,
sections 1.5 and 1.6). On `main`, when the deletes end, two iterations
are done; their cuts wait for the startup pos to pass pEnd (pSafe is
known at 3.25 R and 4.5 R) and then pSafe. Through the drive the startup
section (the stream after the startup pos) is 0.85 to 1.45 MB long, so
each wait takes about 1 MB of growth, 4 to 6 R at this rate. The first
cut, at 7 R, releases 2 MB; the rest of the deleted keys' stream comes
back with the cut of the next iteration, which begins at 6.5 R by the
growth rule, ends at once, and is cut at 14 R, after both waits.

With B the same: M1's rule asks that no done iteration waits for its
cut, and there are such iterations until their waits end, so no
iteration begins by the clock before 6.75 R, when the growth rule begins
one anyway. B moves the begin; the waits that follow it are the stream's
growth, as before. `maintain()` helps a slowly written database by its
take (M4), which moves the startup pos to the waiting position at once,
more than by its begin (M1); B2 adds that take, hence its gain.

### 4. What B2 costs

* **The stream at a large startup distance.** `TwinDriveProbe` on G4's
  twin at sd 50 MB, 300,000 drive transactions: on `main` each 10,000
  wrote 11.0 to 16.6 MB (the values 10 MB); with B2 the same until
  about 160,000, then 34 to 132 MB: 98 to 440 internal records other
  than steps (tables, rows and, most of them, B2's takes), about 150 to
  200 kB each, 95 % index nodes, and more index nodes in the user's
  records too (up to 33 MB). G4's run in section 1 shows the same: the
  twin's stream 4.3 times `main`'s. Argued from these counts, not traced
  node by node: a take is bounded by `MAINTAIN_TAKE_BYTES` (256 kB)
  beyond its first transaction, so moving the startup pos across a
  startup section of about 40 MB takes many takes, one a commit; and
  each is large, as the index bytes of a key overwritten often grow with
  the stream kept (section 6, F2).
* **A promise of the Pub API.** `java/before-commit.sh` on B2: the unit
  test `PubTesterJavadoc.testReclaimCutsLater` fails ("the first cut
  after 16 puts, expected true"): `Database.setRetainDuration()` says
  that nothing is cut before the stream has grown by about four times
  the startup distance, and with B2 the first cut comes after 1.6 MB at
  sd 5 MB. The Javadoc and the test would change.
* **The largest record** (G1 of `count-gates.sh`): 277,468 bytes
  without its values, against 101,696 on `main` (limit 1 MB, margin 3.6
  against 9.8): a take's record. G2, G3, G4 and G5 pass; G3's peak 4.414
  against 4.725.
* **027-13, section 4**: at most six internal transactions after a user
  transaction; B2 adds a seventh (within the margin of 1,024 times and
  top node ordinals).

### 5. The stream's bytes, the proofs and the checks

* **Stream bytes.** B changes the stream only where a quarter of R
  passes before 2 sd of growth and M1's rule holds, a slowly written
  database: in C2 the drive wrote 12.6 MB against 12.0 (+5 %), the twin
  10.9 against 9.8 MB (+11 %; `SlowDriveProbe ... 40 twin`), more
  iterations and their tables and rows. `StreamDigest quick` (11
  configurations, 4 modes): B gives the same digests as `main` in all
  44 (DIGESTS IDENTICAL): its added rule begins no iteration in them.
  B2 differs in l3-node14 and l3-node62 (streams 1.2 % and 1.0 %
  longer), with the four modes the same in each, so restarts do not
  change what B2 writes. G1's run (`count-gates.sh`) differs with B too
  (its largest record 95,248 against 101,696 bytes). The format is the
  same in both.
* **Proofs.** The model leaves out R and the times, the table and
  `maintain()` (027-13, section 5): when an iteration begins and when
  the take runs are outside every theorem. B and B2 begin iterations as
  the rule of 1.3 does (pStart, tStart, pCut, E) at other commits, and
  B2's take is `maintain()`'s M4, a take beyond the share, which the
  model's take policy allows (any pace, `takePolicy`, T3). So no
  statement of T8, T9, T12, T-COVER, T-LATEST or of the contract
  (`cutOK_of_rc`, `rc2_of_iteration`, `iterationOK_of_stepsOK`) changes.
  INV-RESTART: B's rule reads the table and fp only, which a start
  restores (1.9); B2's take also the startup pos, which a start reads
  from the stream; StreamDigest's restart modes agree for both.
* **Checks.** `java/stress/conformance.sh reclaim` (35 traces; C-CUT
  with RC, C-STEP, C-L, the probes after restarts): `CONFORMANCE OK` for
  B and for B2, but its configurations reach neither change: their
  streams stay below 400 kB between iterations, and the traces of B and
  B2 differ only in where the PHYSCUT lines fall (the physical cut waits
  for durability). On traces that reach them, TraceExport with `n=1500
  keys=20 maxnode=8 sd=400000 ops=1 valsize=4000 retain=4 probe=10
  tree=1 steps=1`, seeds 1 and 2 (2 cuts a trace on `main`, 3 with B, 6
  with B2), the checker (`lean/`, `tracecheck`) gives `TRACECHECK OK`
  for all six: RC1 to RC4 at every cut, every step against the model of
  the steps, no probe failure. A configuration of this kind would join
  the reclaim set if B or B2 landed.
* **Gates.** `java/before-commit.sh`: B `BEFORE COMMIT OK (92 s)`; B2
  `BEFORE COMMIT FAILED: unit tests` (section 4). `CountGates all`, as
  `count-gates.sh` runs it: `COUNT GATES OK` on `main`, B and B2.
* **Texts that B changes, if it lands**: 027-13, sections 1.2 (the
  begin), 1.10 (M1's rule shared) and 4 (the pace); `Db.setRetainDuration`
  ("How commits pace reclaim"), `Db.maintain()` (a reclaim iteration
  begins at a commit only after more than twice the startup distance;
  028-06's text) and the class comment of `Reclaim`. The Pub's
  `Database.setRetainDuration()` stays true with B (its test passes).

### 6. Other findings

* **F1. `maintain()`'s M1 stops beginning iterations in a written
  database.** An iteration begins only if lastPStart - fp is at least
  400 kB, and writes change neither: once the last iteration is cut, fp
  is the pStart of the one before it (its own, for the first), so if the
  two began within 400 kB of each other, as when the clock begins them
  about a quarter of R apart in a slowly written database, no iteration
  begins until the growth rule (2 sd) begins one.
  `SlowDriveProbe 50000000 1 300 twin maintain` on `main` (sd 50 MB,
  one key of 900 bytes overwritten 1,000 times an R, `maintain()` until
  false after each commit): after the first cut kept grew to 93 MB by
  90 R, fell to 12 MB when the growth rule began an iteration at about
  100 R, grew again to 98 MB by 180 R, and stayed near 3 MB from 190 R
  on. G5 does not see it: its drive has no writes. B inherits the rule.
  A 028 entry is proposed.
* **F2. The index bytes of a key overwritten often grow with the stream
  kept.** G4's twin at sd 50 MB on `main` (`TwinDriveProbe`): the user's
  records wrote 51 kB of index nodes in the first 10,000 drive
  transactions (11 MB kept) and 5.4 MB in those to 280,000 (267 MB
  kept), half of the values' bytes; consistent with the key node holding
  the key's versions (klongs appended, `KeyNode`) back to the first
  available position. A cost of a long stream kept, not of B.
* **F3.** At C2's settings G4's ST6 gate fails on `main` (section 1).

### 7. Options and recommendation

* **A. As now** (028-06): commits begin iterations on the stream's growth
  (more than 2 sd since the last began, and R/4), `maintain()` calls by
  the clock; the Javadoc of `Db.maintain()` and `Db.setRetainDuration()`
  says so, with C2's figures. No change.
* **B. As registered**: a commit begins an iteration also on M1's rule
  (branch `028-47-b`, da71233b; landing it needs the texts of section
  5). Measured: no clear gain; at G4's own settings nothing changes, at
  C2's settings G4's lag 14.8 R becomes 8.9 R (the gate is 2 R), C2
  itself the same, at sd 50 MB kept at 4 R 270 MB becomes 245 MB. The
  cut still waits for the startup pos, which moves with the stream's
  growth (section 3). It writes up to about 10 % more stream in a
  slowly written database, and it inherits F1.
* **B2. B and `maintain()`'s take at commits** (branch `028-47-b2`,
  cbe46106). Measured: about `maintain()`'s gain at C2's settings (0.63
  MB at 4 R; G4's lag 2.4 R) and at sd 50 MB for the emptied database
  (3.4 MB at 4 R), but the twin at sd 50 MB wrote 4.3 times the stream,
  and a Pub API promise and its test, the largest record and 027-13's
  bound of six transactions change (section 4). Not landable as it is: a
  take at commits needs a bound on what it writes, a design of its own.

Recommended: **A**. B gives no clear gain, and Frans decided on
2026-11-13 that B is taken only for a clear gain (KISS). B2 shows where
the gain is, the take, and costs too much at the Pub's default startup
distance; a take at commits with a bounded cost would be a design item,
not proposed now. F1 limits the recommended way itself, `maintain()` in
a written database, and is worth its own entry.


Log
---

2026-11-24. Registered by lead-1124 (026-13, Q1, option B; 026's
proposals).

2026-11-24. Taken by an agent of lead-1124 (in progress), in a clone of
`main` at 5f8395e7.

2026-11-24. Study done, for Frans (the agent of lead-1124): the Result
above; B (branch `028-47-b`, da71233b) and B2 (branch `028-47-b2`,
cbe46106) kept in the clone, not landed; the entry became a directory
with the probes. Recommended: A, no change; F1 proposed as an entry.
Status open, for Frans's decision. Gates: B `BEFORE COMMIT OK (92 s)`;
B2 `BEFORE COMMIT FAILED: unit tests` (section 4); `CountGates all`
`COUNT GATES OK` on `main`, B and B2; `conformance.sh reclaim`
`CONFORMANCE OK` on B and B2.
