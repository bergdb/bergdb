005-20. Fix: Jmx setRetainDurationInDays computes in int
========================================================

Status: done (2026-10-21). Kind: fix. Created 2026-10-21.

Found on 2026-10-21 in a review of the Java code for overflow, by Claude
(Opus 5.5, Claude Code), at Frans's request; checked with a probe.


The issue
---------

`Jmx.DbMonitor.setRetainDurationInDays(int days)` computes `days * 24 *
3600` in `int`. Up to 24,855 days it is right; 50,000 days gives 289.7
days and 99,999 days 578.5 days, so reclaim cuts history that was asked to
be kept; 30,000 days throws "too small".


The fix
-------

Compute in `long`, with `Math.multiplyExact`, so that a value too large
for a `long` throws instead of wrapping.


Done when
---------

* A unit test with 50,000 and 99,999 days.
* `java/before-commit.sh` prints `BEFORE COMMIT OK`.


Outcome
-------

2026-10-21, by Claude (Opus 5.5, Claude Code). `setRetainDurationInDays`
computes `days * 24L * 3600` and multiplies with `Math.multiplyExact`; more
days than a `long` of time units holds (10,675,200 and more) is an
`IllegalArgumentException`. `setRetainDurationInSeconds` uses
`Math.multiplyExact` too (it was right already). New test
`DbTester.testJmxRetainDurationInDays` (1 to 10,675,199 days, and one day
more). `before-commit.sh`: BEFORE COMMIT OK (947 unit tests, 61 f-tests).
