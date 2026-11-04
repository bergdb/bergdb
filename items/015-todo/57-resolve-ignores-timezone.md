015-57. Fix: time.resolve(TimeZone, String) ignores its time zone
=================================================================

Status: open. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review R8's finding R8-F2 (items/016-release-2026-2/06-reviews/R8.md,
section R8-F2: where, intended, actual, effect, a proposed fix), shown by a
test or probe in 06-reviews/R8/. In 2026.1: yes (`release-2026.1:java/src/bergdb/pub/Time.java`, line 95, the same call).

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).
