028-51. Fix: maintain()'s rule M1 stops beginning iterations in a written database
===================================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-24 by Frans Lundberg.

What: `maintain()`'s rule M1 (`Db.maintain()`, `Reclaim.maintain`;
027-13, section 1.10) begins a reclaim iteration only if the new
iteration's cut would release at least `MAINTAIN_MIN_RELEASE` (400 kB),
that is, only if lastPStart - fp is at least 400 kB, and writes change
neither. Once the last iteration is cut, fp is the pStart of the one
before it (its own, for the first). So if the two began within 400 kB
of each other, as when the clock begins them about a quarter of R apart
in a slowly written database, `maintain()` begins no iteration until
the growth rule of commits (more than 2 sd since the last began) begins
one. Found by 028-47's study, section 6, F1.

Why: `maintain()` is the way that 028-47 recommends, and Frans kept
(028-47, option A), for a database written slowly after a mass delete;
F1 limits it. `SlowDriveProbe 50000000 1 300 twin maintain` (028-47's
`probes/`) on `main`: sd 50 MB, one key of 900 bytes overwritten 1,000
times an R, `maintain()` until false after each commit. After the first
cut kept grew to 93 MB by 90 R, fell to 12 MB when the growth rule began
an iteration at about 100 R, grew again to 98 MB by 180 R, and stayed
near 3 MB from 190 R on. G5 of `CountGates` does not see it: its drive
has no writes.

Frans: none, unless the fix changes what `maintain()` promises; then a
decision, with the options in full.

Done when:

* The entry says, with the sentences quoted, whether F1 breaks what the
  Javadoc of `Db.maintain()` and of the Pub's `Database.maintain()`
  promises (such as "Calls of this method begin iterations and do their
  steps by the clock, without that growth", and the 400 kB of an emptied
  database), and of `Db.setRetainDuration()`; if it does, an RB entry in
  033, with its severity (033's rules: a fault that can be considered a
  bug is registered, Frans, 2026-11-24).
* A fix, with a test that fails before it and passes after it (such as
  F1's case at a size that runs in seconds, or a `CountGates` gate on a
  drive with writes), and the texts that describe M1 (027-13, section
  1.10; the Javadoc) as the code then is.
* `java/before-commit.sh` prints BEFORE COMMIT OK; as the change needs,
  `java/stress/conformance.sh reclaim` CONFORMANCE OK, `StreamDigest`
  (the streams that change, and why), and `java/stress/count-gates.sh`
  COUNT GATES OK.
* If the fix changes what `maintain()` promises: the options in full in
  this entry, status in progress for Frans's decision, nothing landed.

First step: read 028-47's study (sections 3 and 6), 027-13, section
1.10, `Reclaim.maintain` and `Reclaim.cutPending`; run `SlowDriveProbe`
as above, then find a smaller case that shows the stall.


Result
------

Done 2026-11-24 by an agent of lead-1124, on the branch `028-51` of a
clone of `main` at 6d1d7805. The probes: 028-47's `SlowDriveProbe` and
this entry's `probes/IdleLiveProbe.java` (a database with live values
and maintain() calls, no writes). MemoryStream and a test clock; counts
and sizes only, no times.

### 1. The fault

M1 began an iteration only if the new iteration's own cut, the stream
from fp to lastPStart, would release MIN_RELEASE (400 kB); writes change
neither. So once the iteration last cut had its pStart within 400 kB of
its pCut, M1 began none until 1.2's rule of growth (more than 2 sd since
the last began) began one. Two ways in: the first iteration, whose pCut
is its own pStart; and an iteration begun R/4 after one with nothing to
cut (its pCut at fp, such as one that the growth rule began after a
cut), in a database that writes less than 400 kB in R/4. In a database
not written to, the first way keeps for good what an application writes
and deletes after such a cut, if it stays below 2 sd.

### 2. What maintain() promises, and F1

The Javadoc of release 2026.6, the same on `main` before the fix:

* `Db.maintain()`: "Calls of this method begin iterations and do their
  steps by the clock, without that growth. So they help a database that
  the application no longer writes to, and one that it writes to slowly
  after deleting much". Broken: after such a cut the calls begin no
  iteration until that growth; in F1's run (sd 50 MB) the stream kept
  grew to 110 and 115 MB between the growth rule's iterations.
* `Db.maintain()`: "Called again and again, with time passing, it brings
  a database that has been emptied to within about 400 kB of the stream
  of a fresh one". Broken for a database emptied after such a cut:
  `testEmptiedAgainAfterACut` (section 5) kept 4,855,184 bytes after 10 R
  of calls, its twin 326,608; no iteration began, and none would.
* The Pub's `Database.maintain()`, which calls `Db.maintain()`: "An
  application that has deleted much and then writes little or nothing
  can call this method, now and then, to have the space back without
  writes of its own. Called again and again, as time passes, it brings a
  database that has been emptied to within about 400 kB of the size of a
  fresh one". Broken in the same case.
* `Db.setRetainDuration()`: "maintain() begins iterations by the clock,
  without commits (bergdb 026-13, U13-4)"; the Pub's
  `Database.setRetainDuration()`: "A database that is not written to
  does none of this by itself; maintain() lets the application ask for
  it (bergdb 024-32)". Broken as above.
* What the Javadoc of `Db.maintain()` says of M1's rule, "the new one's
  cut would release at least 400 kB", is what the code did, and "the
  400 kB of an emptied database" is that rule's reason; the promises
  above are what failed.

So F1 breaks what maintain() promises: RB-006 in 033, S4 (disk space
only: nothing lost or wrong, the database goes on, and the commits' rule
gives the space back after 2 sd of growth). Released in 2026.5, where
`maintain()` came (024-32), and 2026.6.

### 3. The fix

M1 begins an iteration also when the next iteration's cut would release
MIN_RELEASE: when the stream written since the table was last stored is
at least MIN_RELEASE (`Reclaim.maintainBeginDue`; `tablePos`, the
position of the table's value at the latest state, read from the index,
so that a start gives the same, INV-RESTART). With no iteration running
and no cut pending, reclaim's last record is a store of the table (the
last iteration's end, markSafe or cut), so the stretch is what others
wrote: nothing in a database that is not written to, where the calls
stop as before. 027-13, 1.10.

Two rules without the lookup were tried and dropped, as they make a
database with live values that is not written to rewrite them again and
again, each iteration's cut releasing only the copies of the one before
(`IdleLiveProbe`, 20 R of calls after the puts):

* counting the stream since the last pStart: from 3,000 live keys
  (427 kB of stream), 3.1 MB written in the last 10 R, nothing on
  `main`; it was the first version, gated with BEFORE COMMIT OK, COUNT
  GATES OK and CONFORMANCE OK before this was seen;
* counting from the last iteration's pSafe: from 300,000 keys (45 MB),
  81 MB in the last 10 R, as the takes after pSafe write more than
  400 kB.

With the table's position every such run wrote what `main` writes:
3,000, 8,000, 15,000, 100,000 and 300,000 keys after the puts, nothing
in the last 10 R; and 3,000, 8,000 and 30,000 keys after 10 rounds of
overwrites at sd 1 MB, nothing at 3,000 and 8,000, 24.5 MB in the last
10 R at 30,000 in both: there M1's first rule already rewrites a live
set whose iterations each write 400 kB or more, on `main` as before.
Not changed here; a note for a later entry.

What `maintain()` promises does not change: the fix gives back the
promises of section 2, and the calls stay quiet where they were (G5 and
the runs above), each call's work and the meaning of its return as
before. The texts that describe M1 say "its cut, or the next one's": the
Javadoc of `Db.maintain()` (and the rule in its second paragraph), of
the Pub's `Database.maintain()`, of `Reclaim.maintain` and
`MAINTAIN_MIN_RELEASE`; 027-13, sections 1.10, 6, 7 and 10.

### 4. Measured

`SlowDriveProbe` (028-47's probes), kept in MB, `main` and the fix:

* F1 as registered (`50000000 1 300 twin maintain`): `main` 0 to 115 in
  cycles until 200 R, then 2.3 to 3.3; the fix at most 3.4 throughout,
  2.2 to 3.2 from 50 R.
  The drive wrote 320 MB against 352: the user's index bytes 0.2 MB
  against 15.4, as a key's index bytes grow with the stream kept
  (028-47, F2).
* With the deletes (`50000000 1 300 maintain`): `main` 2.0 to 114.6
  until 200 R, then 2.3 to 3.2; the fix 1.4 to 5.9 until 50 R, then 2.2
  to 3.2.
* sd 5 MB (`5000000 1 30 maintain`, with and without twin): `main` up to
  12.6; the fix 1.5 to 3.6.
* C2 (`1000000 5 40 maintain`): `main` 1.23 at 2 R, 0.68 at 4 R, 1.92 at
  10 R, 0.58 to 2.66 from 20 to 40 R; the fix 1.23, 0.68, 0.95 and 0.50
  to 1.18. The Javadoc's "1.2 MB were kept at 2 R" holds.

### 5. Tests

`ReclaimMaintainTester`:

* `testSlowlyWritten`: sd 5 MB, a value of 10 kB every 10 ms (1 MB an
  R), maintain() until false after each commit, 30 R; the stream kept
  after the first cut at most 4 R of writes and 600 kB. `main` 12.1 MB,
  fails; the fix 3.5 MB.
* `testEmptiedAgainAfterACut`: sd 5 MB, 4,000 keys put and deleted,
  calls until the first cut, 20,000 keys put and deleted, 10 R of calls
  with no writes; kept at most twice the twin's and 600 kB, quiet in the
  last 3 R. `main` fails (section 2).
* `testLiveDatabaseQuiet`: 5,000 live values, sd 5 MB, 10 R of calls;
  nothing written in the last 5 R. Passes on `main`, fails with the rule
  from pStart (5.8 MB in the last 5 R).

The conformance's reclaim set has `r-maint-sd`: maintain() after every
transaction, sd 400 kB, values up to 4 kB, R = 4 s; 8 cuts a trace
against 6 on `main` (seeds 1 to 3), TRACECHECK OK.

### 6. Gates

On the clone, the fix on `6d1d7805`, at a low priority (`nice`):

* `java/before-commit.sh`: `BEFORE COMMIT OK (62 s)`.
* `java/stress/count-gates.sh all`: `COUNT GATES OK`; G5 the same as on
  `main` (kept 80,600 bytes against the twin's 800, the last call with
  work 3,006 of 20,000).
* `java/stress/conformance.sh reclaim`: `CONFORMANCE OK`, 40 traces with
  `r-maint-sd`, `TRACECHECK OK: 40`.
* `java/stress/level3.sh` (reclaim's level, full): `LEVEL 3 OK`.
* `java/stress/apps.sh quick` (the user apps, five of which call
  `maintain()`): `APPS OK`.

Again after the branch was rebased onto `main` at `16093dd6` (028-50,
028-52 and 034 landed meanwhile): `BEFORE COMMIT OK (60 s)`, `COUNT
GATES OK` (G5 as above), `CONFORMANCE OK` (reclaim, 40 traces).

StreamDigest quick, the clone's jar against `main`'s, with `main`'s
compiled class: DIGESTS IDENTICAL (44 of 44): its workloads do not call
`maintain()`, and M1 is `maintain()`'s only.


Log
---

2026-11-24, 12:30. Registered by an agent of lead-1124, from 028-47's
finding F1 (Frans, 2026-11-24, 12:30).

2026-11-24, 12:35. Taken by an agent of lead-1124 (clone c51b, branch
028-51).

2026-11-24. Done by the same agent, on the branch `028-51`: M1 begins an
iteration also when the stream written since the table was last stored
would be released by the next iteration's cut (`68386bc6`); F1 broke
what the Javadoc of `maintain()` promises, RB-006 in 033 (S4); three
tests in ReclaimMaintainTester, `r-maint-sd` in the conformance's reclaim
set, the entry a directory with `probes/IdleLiveProbe.java`; RB-006 in
the section "After the release" of 2026.6's and 2026.5's notes and in
`releases/next.md` (033's rule of 2026-11-24). Gates:
BEFORE COMMIT OK, COUNT GATES OK, CONFORMANCE OK (reclaim), LEVEL 3 OK,
APPS OK; StreamDigest quick DIGESTS IDENTICAL.
