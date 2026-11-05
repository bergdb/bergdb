015-57. Fix: time.resolve(TimeZone, String) ignores its time zone
=================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

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

2026-11-05. Done in night 006-12. Verified with R8's test, made
`Time.testResolveUsesTheTimeZone` (in `Time`, beside its other resolve
tests, with a winter time too): before the fix "Expected 2013-08-19
12:29:00.0000000, got 2013-08-19 14:29:00.0000000."; it passes after.

* Fix, R8's: `Time.resolve(TimeZone, String)` passes its zone to
  `TimeResolver.resolveAbsolute`, as `resolve(TimeZone, Time, String)`
  does; `Time.utc(String)` keeps UTC. A null zone is now refused with
  `IllegalArgumentException` (`TimeResolver`'s check, as the three-argument
  method), where it was ignored; the Javadoc says so.
* 010-01: no setting, method or state. The stream's bytes are unchanged
  (P2): the Core does not call it, and StreamDigest's workloads use the
  Core API.
* Tests: the new test; `Time` (15) and `PubTester` pass.
