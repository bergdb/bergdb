015-04. Investigate: deps.py counts TransSeq.take and dither as test code
=========================================================================

Status: open. Kind: Investigate. Created 2026-11-03 by Frans Lundberg.

What: `java/deps.py`'s helper rule counts `TransSeq.take` and `dither` as
test code, because only tests call them from outside their own file. It
is harmless for `deps.py`'s own check, but a trap for any check that
reuses its markers, such as 005-79's doubles check (which needs a
`__main__` guard and a `helpers` flag in `deps.py`).

Questions: is the rule wrong, or only its name? Which other production
methods does it count as test code?

Done when: the rule is corrected or documented, with the list of methods
it misclassifies.

First step: run the rule's classification over `java/src` and compare it
with the callers.

Not a fault of the database. Not for 2026.2 unless 005-79's check depends
on it. Found 2026-11-03 in 005-79's plan.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).
