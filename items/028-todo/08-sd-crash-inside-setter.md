028-08. Investigate: a crash inside setStartupDistance's own record
===================================================================

Status: open. Kind: Investigate. Frans: none.
Created 2026-11-13 by Frans Lundberg.

The task is to find out whether this is a bug (Frans, 2026-11-13, 13:04:
"Add these as todo items. The is to evaluate whether or not they really
are bugs.").

What: the draft of 027-11 (Startup) found that a crash inside the record
that `Db.setStartupDistance` writes, after the meta block written within
that record, makes recovery abort the record, while the start then takes
the new startup distance from that meta block (027-11, sections 1.2 and
1.4, at 7e190010).

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


Log
---

2026-11-13. Registered by coord-1113, from the draft of 027-11 (Frans, 13:04).
