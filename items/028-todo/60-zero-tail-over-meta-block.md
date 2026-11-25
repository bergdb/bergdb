028-60. Fix: after a kill, a zeroed tail over a meta block stops the start
=========================================================================

Status: in progress. Kind: Fix. Frans: none, unless the fix needs a choice of
what the start takes as a cut tail (then options here).
Created 2026-11-25 by Frans Lundberg.

What: 031-02's app hunt, finding F1 (section 5): three times in about
9,500 kills of a writing process (SIGKILL, macOS, APFS), the last stream
file ended in zeros within its length, from a page boundary on (115 to
459 kB). Where the zeros cover a meta block's position, the next start
throws `StreamFormatException: Invalid magic bytes in stream: ... not a
BergDB stream, or it is damaged; or an earlier release ... encrypted
it` (from `Db.refuseOtherNodeSize`, which reads the last meta block
before recovery), and the database does not start until a person cuts
the file; cut at the record that the zeros reach, it starts with every
transaction a sync returned for. A zeroed tail that ends before the
next meta block is recovered as a cut tail. The system makes the zeros
(031-02's `ZeroTailProbe`: plain `RandomAccessFile` appends and forces,
1 in 150 kills). Release 2026.6 refuses the same files.

Why: the Javadoc of `Database` ("What a crash keeps") says that a crash
cuts the stream's tail and the start recovers it; only a power loss is
said to leave a tail of zeros, refused with "Bad transaction size in db
stream, S, spos P" and the advice to cut at P. A database that does not
start after a process kill is S2 (033's rules); in 2026.6, a released
bug.

Frans: none, unless the fix needs a choice (above).

Done when: the refusal reproduced from the kept files and from a unit
test (a zeroed tail over a meta block, on a file stream); its cause
named in the start's order of reads; a fix with which such a tail is
recovered as the Javadoc says, or, if that needs a choice of what the
start may take as a cut tail, the options written here; a unit test
that fails before the fix; `java/before-commit.sh` printing `BEFORE
COMMIT OK`; the kill-restart harness (`java/stress/kill-restart.sh`)
and 031-02's KillWriter run; an RB entry drafted for 033.

First step: 031-02, section 5, F1; `Db.refuseOtherNodeSize` and the
start's recovery of a cut tail (027 parts on the stream and startup:
027-03, 027-11); the Javadoc of `Database` and `FileStream`.


Log
---

2026-11-25. Registered by lead-1125, from 031-02's finding F1.
