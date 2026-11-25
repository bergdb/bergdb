028-58. Investigate: maintain() leaves an emptied database at 790 kB, two stretches each below 400 kB
=====================================================================================================

Status: done: no new released bug; on 2026.5 and 2026.6 the 790 kB are
RB-006's and RB-007's; on `main` RB-007's, and a rest of RB-006 that
028-51's fix leaves. Kind: Investigate. Frans: none.
Created 2026-11-25 by Frans Lundberg.

What: `maintain()`'s M1 (`Reclaim.maintainBeginDue`; 027-13, section
1.10) tests its two stretches one by one, the stream from fp to the
last pStart and the stream written since the table's last store, so
each can stay just below MIN_RELEASE (400 kB) for good. Found by the
review in 031-03 (section 9.1): `TwoStretchProbe 390000 390000 390000
10000 20000` (a value put and deleted on each side of the second
iteration's pStart) keeps 790,264 bytes on `main` after 20 R of calls,
789,560 more than a fresh database; 028-53's B keeps the same; 031-03's
one threshold (its R4) keeps 19,480.

Why: the Javadoc of `Db.maintain()` and `Database.maintain()` says the
calls bring an emptied database to within about 400 kB of a fresh
one's stream; 024-30's G5 allows 600 kB. If 2026.5 and 2026.6 keep the
same, a released bug (033's rules; S4, disk space only, as RB-006 and
RB-007).

Frans: none for the investigation. The fix goes with RB-007's (031-03,
decided by Frans), unless he decides otherwise.

Done when: `TwoStretchProbe` (031-03's probes) run on `main`, 2026.6
and 2026.5, the bytes kept quoted; whether it breaks the Javadoc; if
so, an RB entry drafted for 033; the fix named (031-03's R4, or a
change of `main`'s M1 alone) with what it costs.

First step: 031-03, sections 3.4 and 9.1, and its `TwoStretchProbe`.


Result
------

Investigated 2026-11-25 by an agent of lead-1125, on the branch
`028-58`, at `0cc8071f`, with the tags `release-2026.6` and
`release-2026.5` built in worktrees. The probe is a copy of 031-03's,
`probes/TwoStretchProbe.java`, with one argument more, `after`: `/d` put
and deleted after the calls have cut iteration 2, not while it waits
for its cut. Bytes kept: the stream from the first available position
to its end; fresh: a new database's.

* **031-03's case** (`TwoStretchProbe 390000 390000 390000 10000
  20000`):
  * `main`: 790,264 kept, fresh 704 (789,560 more).
  * 2026.6: 790,264 kept, fresh 704, the same rows.
  * 2026.5: 595,872 kept, fresh 200,736 (395,136 more). Not the same
    case: 2026.5's `setStartupDistance` raises 10,000 to 400,000 and
    puts 200 kB live at `/#i/-dummy`, so no iteration begins at `/a`.
  * On `main` and 2026.6 the stream kept is fp 391,400 to the last
    pStart 785,872 (394,472 bytes) and `/d` after it, written while
    iteration 2 waited for its cut; the cut stored the table after it.
    `main`'s second stretch, from the table's last store, does not hold
    `/d`: it is RB-007's case (an iteration that began within 400 kB of
    its pCut, the writes made before its cut), not two stretches below
    400 kB each.
* **Two stretches on `main`** (`TwoStretchProbe 395000 393000 380000
  196000 20000 after`): iteration 2 begins at 793,872 with pCut 396,400
  and is cut; then `/d`, 380,000 bytes, is put and deleted.
  * `main`: 783,472 kept, fresh 704 (782,768 more): 397,472 from fp to
    the last pStart and 386,000 after it, of which `/d`, about 381 kB,
    after the table's last store (the cut, at 798,584); no call did
    anything in the last 20 R. Each of M1's two tests is below 400 kB.
  * 2026.6: 783,472 kept, the same; there M1 counts only the first
    stretch, RB-006's case (the cut iteration began 397,472 bytes after
    its pCut).
  * 2026.5 (`TwoStretchProbe 395000 393000 580000 196000 20000
    after`): 786,608 kept, fresh
    200,736 (585,872 more), RB-006's case: the first iteration, its
    pStart 990,112 its pCut, and `/d` after its cut. `main` keeps 20,976
    there.
  * The case needs commits after the cut that begin no iteration (less
    than 2 sd since the last pStart, or within R/4 of it): with sd 10,000
    `/d`'s commit begins one, and `main` and 2026.6 keep 402,432.
* **The promises.** The Javadoc of `Db.maintain()` and
  `Database.maintain()` says that the calls bring an emptied database to
  within about 400 kB of a fresh one's stream (2026.6 and `main`), "to
  about the size of a fresh one" (2026.5). 783 to 790 kB more than a
  fresh database breaks it, on all three. `MAINTAIN_MIN_RELEASE`'s
  comment and 027-13, section 1.10, describe `main`'s two tests as the
  code makes them; they promise nothing of the sum.
* **Released bug: not a new one.** In 2026.5 and 2026.6, M1 counts
  only the stream from fp to the last pStart, so every case of an
  emptied database kept above that is RB-006's (written after the cut)
  or RB-007's (written before it); both are registered, S4. On `main`,
  028-51's fix (`68386bc6`, RB-006) counts the stream after the table's
  last store by a threshold of its own: when less than 400 kB is
  written after the cut and the stretch before it is just below 400 kB,
  an emptied database keeps up to about 800 kB. So RB-006 is fixed on
  `main` only in part; its entry in 033 needs a line for the rest
  (S4, as RB-006).
* **The fix.** 031-03's R4, one threshold on the stream kept from fp
  with w, ends both cases (19,480 kept in 031-03's case) and RB-007:
  the fix goes with RB-007's. A change of `main`'s M1 alone, one test of
  L - fp without w, would count the last iteration's own rewrites, every
  live value, and rewrite them again and again in a database not
  written to (027-13, section 1.10; 028-51 measured it); to tell those
  from the application's writes needs w, which is 031-03's design.


Log
---

2026-11-25. Registered by lead-1125, from 031-03, section 9.1.

2026-11-25. Done, by an agent of lead-1125 on the branch `028-58`: the
probe run on `main`, 2026.6 and 2026.5, with a variant that writes after
the cut; no new released bug (RB-006, RB-007); RB-006 fixed on `main`
only in part.
