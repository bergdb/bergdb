028-70. Investigate: a start refused after its recovery has written changes the stream
======================================================================================

Status: open. Kind: Investigate. Frans: none.
Created 2026-11-27 by Frans Lundberg.

What: a start can be refused after its recovery has already written to
the stream. The case found: the stream's last committed record has a
format version that this release does not read. The recovery runs
first and may append (it completes the stream's tail), and since
028-60's part 2 (`ac33aa93`) the first append also cuts a tail of zeros;
then the start is refused for the version. `main` before 028-60's part 2
behaved the same way for the recovery's own appends.

Why: a refused start should leave the storage as it found it, as the
other refusals do (015-05; `testRefusedStartsKeepZeroTail` for the
refusals before the recovery). The message of this refusal does not say
that nothing was written, and 027-11 says that the recovery may append
first, so no document is wrong; it is the behaviour that is uneven.
Found by Codex's third review of 028-60's part 2 (2026-11-27), not
fixed there: the fix changes the order of the start.

Frans: none.

Done when: every refusal of a start that can be decided from what is
read comes before the recovery's first write, with a test for the
unreadable format version (the files unchanged after the refused
start); or the cases that cannot be moved are listed in 027-11 with the
reason.

First step: list the checks of `DbStarter` and `Db.startInner` that
come after the recovery's first append, and for each what it reads.


Log
---

2026-11-27. Registered by lead-1127.
