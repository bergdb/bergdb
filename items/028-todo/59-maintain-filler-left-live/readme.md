028-59. Investigate: a stop or a crash between the filler's put and delete leaves it live
========================================================================================

Status: done: a released bug of 2026.5 and 2026.6, S4, for the lead to
register in 033: the Javadoc says that the filler is deleted at once,
and after a stop or a crash between its two records it is not; 027-13,
section 2, corrected. Kind: Investigate. Frans: none.
Created 2026-11-25 by Frans Lundberg.

What: `maintain()`'s filler (M5, 024-32) is a put of
`/#i/dreclaim/-fill.txt`, up to 200 kB of zeros, and a delete of it in
a later record. A stop or a crash between the two leaves it live until
another filler is needed, though 027-13, section 2, says that it is
never live after a call. Found by the review in 031-03 (section 9.2):
`StopAtProbe 10 100 20000` in `main`'s mode: after the stop and 20,000
calls, the filler is live, 199,672 bytes kept. 031-03's design stores
the filler as the table padded with spaces, one record with nothing to
delete.

Why: a document of the code (027-13) that the code does not meet, and
up to 200 kB kept in a database that should return to empty; whether
it breaks a promise of the Javadoc (within about 400 kB of a fresh
database, with other overheads) decides whether it is a released bug.

Frans: none for the investigation. The fix goes with RB-007's (031-03),
unless he decides otherwise.

Done when: `StopAtProbe` run on `main`, 2026.6 and 2026.5, with a stop
and with a crash; whether a promise of the Javadoc is broken; if so,
an RB entry drafted for 033; 027-13, section 2 corrected to what the
code does, or the fix named.

First step: 031-03, sections 3.2 and 9.2, and its `StopAtProbe`;
024-32 (M5).


Result
------

Investigated 2026-11-25 by an agent of lead-1125, on the branch
`028-58`, at `0cc8071f`, with the tags `release-2026.6` and
`release-2026.5` built in worktrees. The probes, in `probes/`:

* `StopAtProbe.java`, a copy of 031-03's without w (only the
  prototype has it), with a crash as well as a stop. At record j, from
  the hook after the record: a stop, `Db.stop()`; or a crash, the
  stream copied as it is 100 ms after the record (the write buffer's
  time is 10 ms) and started. Then 20,000 calls, 1 ms apart, R = 1 s.
  With K2 and V2, the started database is written to and emptied again
  (K2 values of V2 bytes put, then deleted) before the calls. The
  startup distance as `b10`: set by the builder in 2026.5, where the
  setter raises it to 400 kB and puts 200 kB live at `/#i/-dummy`, which
  every iteration rewrites, so that no filler is needed; by the setter
  in 2026.6 and `main`, which have no such builder method (028-13).
* `FillerKillProbe.java`: a child JVM runs the scenario on a
  `FileStream` and halts (`Runtime.halt`) 100 ms after the filler's
  put; the parent starts the directory and makes 20,000 calls.

Bytes kept: the stream from the first available position to its end.

* **031-03's case, interrupted at each record** (`StopAtProbe b10 100
  20000 1 all stop|crash`): 9 records; at the filler's put (record 6)
  the filler is live at the start and after the calls, on all three,
  stop and crash alike; at no other record.
  * `main`: 199,672 kept, filler live; without the stop 199,808, the
    filler deleted; fresh 960.
  * 2026.6: the same, 199,672 and 199,808; fresh 960.
  * 2026.5: 200,112 kept, filler live; without the stop 200,248; fresh
    496.
* **A killed JVM** (`FillerKillProbe DIR b10 100 20000`): the child
  halted at a stream of 200,320 bytes; started, the filler live; after
  the calls live, kept 199,672 (`main`, 2026.6) and 200,112 (2026.5).
* **Written to and emptied again after the stop** (`StopAtProbe b10 100
  20000 1 filler stop|crash 300 1000`: 300 values of 1,000 bytes):
  * `main`: 856,176 kept, filler live; without the stop 284,416.
  * 2026.6: the same, 856,176 and 284,416.
  * 2026.5: 867,120 kept, filler live; without the stop 333,656.
  * The rows show RB-007's case: the last iteration began 386,424 bytes
    after its pCut (`main`), and the writes made while it ran and waited
    for its cut, with its 197,687 bytes of rewrites, nearly all the
    filler, are
    counted by no test of M1. With 2,000 values the stop kept less than
    the run without it (206,984 against 317,072 on `main`); with one
    value of 150,000 bytes the same (354,232 against 354,736).
* **What the filler costs while live.** 200 kB of live value, which
  each iteration rewrites, until a later call needs a filler and its put
  and delete replace it; in a database not written to, for good. Alone
  it keeps no more stream than the run without the stop: the filler's
  bytes stay in the stream there too, deleted.
* **The promises.** The Javadoc of `Database.maintain()` says that a
  call writes "one filler of at most 200 kB that is deleted at once";
  `Db`'s Javadoc says that `maintain()` keeps its filler under
  `/#i/dreclaim/` "deleted at once", and that `getMany()` returns
  BergDB's keys and `getKvCount()` counts them. After a stop or a crash
  between the two records the filler is not deleted: a Core user sees a
  KV of up to 200 kB more, for good in a database not written to. That
  breaks what the Javadoc says, in 2026.5 and 2026.6: a released bug.
  The space promise, within about 400 kB of a fresh database (2026.6,
  `main`; "about the size of a fresh one" in 2026.5), is not broken by
  the filler alone (199,672 kept); with RB-007 the stop leads to more
  (856,176), but RB-007 breaks it without the filler too. A stop lands
  there from another thread as well, read from the code, not run:
  `stop()` takes no lock, and the delete, a transaction of its own,
  does not start after it.
* **Severity: S4.** No value of the application's lost or wrong, the
  database goes on; a 200 kB KV of BergDB's own and its rewrites.
* **Stale texts.** 027-13, section 2 ("never live after a call"),
  corrected. 027-03, section 15 (`/#i/dreclaim/-fill.txt`, "never live
  after the call") and the comment of `Reclaim.MAINTAIN_FILL_KEY_NAME`
  ("Never live after a call") say the same; not changed here (027-03
  and `java/src` were outside this entry's work).
* **The fix.** 031-03's R2 stores the filler as the table padded with
  spaces, one record with nothing to delete, which the next store of
  the table replaces (031-03, section 9.2); it goes with RB-007's fix. A
  stream of 2026.6 with a filler left live keeps it under that design,
  unless the landing deletes a live filler once.


Log
---

2026-11-25. Registered by lead-1125, from 031-03, section 9.2.

2026-11-25. Done, by an agent of lead-1125 on the branch `028-58`: the
probe run on `main`, 2026.6 and 2026.5, with a stop, a crash (a copy of
the stream) and a killed JVM; a released bug, S4, drafted for 033 by the
lead; 027-13, section 2, corrected.
