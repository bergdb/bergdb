028-08. Investigate: a crash inside setStartupDistance's own record
===================================================================

Status: done. Kind: Investigate. Frans: none.
Created 2026-11-13 by Frans Lundberg.

The task is to find out whether this is a bug (Frans, 2026-11-13, 13:04:
"Add these as todo items. The is to evaluate whether or not they really
are bugs.").

What: the draft of 027-11 (Startup) found that a crash inside the record
that `Db.setStartupDistance` writes, after the meta block written within
that record, makes recovery abort the record, while the start then takes
the new startup distance from that meta block (027-11, sections 1.2 and
1.4, at c82bce56).

Why: if so, an aborted transaction has a lasting effect: the setting is in
force although the transaction that set it never committed. That may be
harmless (the setting is not data) or a breach of the commit rule; it is
not known which.

Frans: none; the evaluation's answer is the result: a bug, or intended,
with the reason.

Done when: a test that crashes (truncates the stream) inside the setter's
record, after its meta block, then starts and reads the startup distance
in force; it says which it is. If a bug, a fix with that test and
`java/before-commit.sh` OK; if not, a sentence in 027-11 and in the
setter's Javadoc.

First step: read `Db.setStartupDistance` and where the start reads sd
(`DbStarter`, `MetaBlock`).


Result
------

Verdict: **not a bug**, because the startup distance is a setting, not
data: a crash inside the call leaves the old or the new setting, both
valid (clamped to 400,000 bytes to 10^9), and the stream is valid under
either, as the take keeps the startup section within the deadline for any
setting (`T3_take`, 007-08). A caller whose process stopped inside the
call cannot tell the cases apart in any way: a crash just after the
record's end, before the call returns, gives the new setting too. The
commit rule is about transactions; the dummy value's transaction is
aborted as it should be, and the Core never reads the dummy value.

The test, `DbTesterRestart.testCrashInsideSetStartupDistance`: a database
with sd 1,000,000 and a key, then `setStartupDistance(2,000,000)`; copies
of the stream cut at five places, each started twice (the second start
checks that the setting lasts):

* not cut: sd 2,000,000, the dummy value there;
* 8 bytes before the record's end, and just after the meta block inside
  the record: sd 2,000,000, the record aborted (no dummy value), the key
  there;
* one byte before the block's end, and at the block's start: sd
  1,000,000 (recovery completes the cut block as an invalid one, so the
  last valid block is the one before).

Recorded: a sentence in 027-11, section 1.4, and in
`Db.setStartupDistance`'s Javadoc.

Log
---

2026-11-13. Registered by coord-1113, from the draft of 027-11 (Frans, 13:04).

2026-11-13. Done by an agent of coord-1113 (startbugs, branch
028-startbugs): the test, not a bug, the sentences in 027-11 and the
Javadoc; `java/before-commit.sh` printed `BEFORE COMMIT OK`.
