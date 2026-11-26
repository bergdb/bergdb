028-54. Investigate: a stop or a crash inside a commit's maintenance changes the stream
======================================================================================

Status: open. Kind: Investigate. Frans: answers.
Created 2026-11-25 by Frans Lundberg.

What: on `main`, a crash, or a `stop()` that interrupts reclaim's work
after a user transaction's record (`Db.executeInner` lets a stop do
that), between a user record and reclaim's records after it, gives a
stream that differs from the uninterrupted run's from that record on:
reclaim's interrupted work (a begin, a step) goes on at the next commit,
at other positions (027-13, section 1.2). Found by 031-01's revision
after Codex's review (031-01, sections 4.3 and 10, `MidCallProbe`, a
crash between a user record and the begin of its iteration); on `main`
and on 031-01's prototype alike.

Why: 010-01, P2: the stream's bytes are a function of the accepted
transactions, "not of timing, threads, restarts"; Frans's goal of
2015-12-28, "a restart can be inserted between any two transactions
without affecting the bytes in the stream". P2 is checked at calls
(INV-RESTART, StreamDigest, RestartInvariance), not inside a commit's
maintenance. If a stop or a crash there breaks a promise of the
README or the Javadoc, it is a released bug (033's rules).

Frans: answers. Does P2's "between any two transactions" cover a
restart between a user transaction and reclaim's internal transactions
that follow it, after a stop, after a crash, or both?

Done when: `MidCallProbe` (031-01's probes) run on `main` for a crash
and for a `stop()`, at each kind of reclaim record that can follow a
user record (a begin, a step, a cut, a table store), with the bytes
compared; what the README, `Db`'s and the Pub's Javadoc promise of the
stream after a stop and after a crash, quoted; an RB entry in 033 if a
promise is broken; with Frans's answer, a fix as a 028 entry or the
reason it stays, written here.

First step: 031-01, sections 4.3 and 10, and `MidCallProbe`; 010-01,
P2 and P7; 027-13, sections 1.2 and 9 (INV-RESTART).


Log
---

2026-11-25. Registered by lead-1125, from 031-01's revision.

2026-11-26. Answered by 031-05's direction (Frans, 2026-11-26): every
write to the stream a function of the stream and the user actions, a
restart, a stop or a crash inside a commit's maintenance included.
