015-56. Fix: a refused second start() of one builder closes the running database's stream, and the database fails
=================================================================================================================

Status: open. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

For 2026.2: new in this release (2026.1 refused the second start another way).

What: review R8's finding R8-F10 (items/016-release-2026-2/06-reviews/R8.md,
section R8-F10: where, intended, actual, effect, a proposed fix), shown by a
test or probe in 06-reviews/R8/. In 2026.1: no, not this way: there `dir()` opened the `FileStream` and a second `start()`

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: the test of R8-F10, in a tester of the area.


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).
