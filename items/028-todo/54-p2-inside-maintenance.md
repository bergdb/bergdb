028-54. Investigate: a stop or a crash inside a commit's maintenance changes the stream
======================================================================================

Status: done 2026-11-27. Kind: Investigate. Frans: answered.
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

2026-11-27. A1 is (e), one record an action (Frans; 031-06, section 8):
an action's record holds its maintenance, so no record comes between a
user's record and its maintenance, and a crash or a stop cannot land
there. On the prototype, 27,720 crashes, failures and stops at record
boundaries continued to the uninterrupted stream (031-06, section 4.1).
`main` has the fault until 031-06 lands. Still open: whether the README's
sentence ("The same transactions in the same order give the same bytes")
makes it a released bug for 033.

2026-11-27. Done. Frans's answer (2026-11-27): P2 covers a restart
after a stop, so a stop between a transaction's record and reclaim's
records after it breaks P2 and the README's sentence: RB-013, S4,
registered in 033 (17:12). The crash case is not counted: a crash may
leave a partial append, and the bytes after a crash are not promised
(16:41; 031-06's `p2-draft.md`). Fixed on `main` for 2026.7 by 031-06,
one record an action, merged on 2026-11-27 (`5b88cc80`). Moved to
Closed.
