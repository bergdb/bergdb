018-08. Harness 6.6: concurrency
================================

Created 2026-11-06 by Frans Lundberg, as harness 6.6 of 018-01 (W2), in
the day 006-13 (Frans, 2026-11-06, 11:46, on harness 6.6's scope: "As you
recommend.": Option 1).

**Status: the eight jcstress tests rerun on `main` (`e446bb2`) on s1 in
default mode: each `[OK]`, no FORBIDDEN outcome in 0.46 to 6.9 billion
samples a test (section 3). On F53, on release 2026.3's commit A (929fa33), in the night of
2026-11-06 to 07: 8 of 8 OK (006-13, Outcome). Done; 018 closed
2026-11-07.** No test
added: review R7 of 006-13 (2026-11-06, the night's concurrency fixes
015-66, 67, 70, 80 and 82) has no A finding, no cycle in its lock-order
table, and no shared field that needs a new jcstress test.


## 1. What it checks, and why

Harness 6.6 is Option 1 of 006-13 (W2b): the jcstress tests of
`java/stress/jcstress/`, which test the publications of the lock-free fast
path between two threads against BergDB's real classes, rerun on today's
code, in jcstress's default mode, on F53 (AArch64, which reorders) and on
s1 (x86, which hides most reorderings; 009-03, section 2). A test passes
when no outcome it marks FORBIDDEN is seen.

The eight tests:

* `HandlePublication`, `InstallPublication`, `EvictionRace`,
  `ValuePublication`: the barriers of the fast path (009-02, sections 3.4
  and 3.5).
* `GrowthPublication`: a key node's growth against a reader (015-12).
* `SwizzleOrder`, `TopSwizzleOrder`: a swizzle against a fast-path read,
  in a key node and in a top node (015-14).
* `PlainPublication`: the control, a plain store and a plain read; its
  race (outcome 0, ACCEPTABLE_INTERESTING) shows that the harness can see
  one. Seen on F53, never on s1 (009-03, section 2).

Known faults of the class (018-01, section 6.6): 015-35, 80 and 82, and
015-12 and 015-14, fixed. The jcstress tests reach 015-12 and 015-14 (each
test failed on the code before its fix: 015-12 and 015-14, their Logs); 015-35,
80 and 82 are in `Db`'s close, `BufferedStream` and storage's threads,
which these tests do not build.

When they last ran:

* The five of 009 in default mode on 2026-11-03: on F53 on `6f932f0` and
  on s1 on `3e32f02` (016-08, F1 and L3), after the eviction thread's new
  wake (`988fe1a`, 005-65), no forbidden outcome.
* `GrowthPublication`, `SwizzleOrder` and `TopSwizzleOrder` only in quick
  mode on F53 (2026-11-03, 015-14's Log); 016-08's F6 and L5, which were
  to run them in default mode, did not run. So today's s1 run is their
  first in default mode.
* Since then: 015-14's acquires on the fast path (`4e10aa2`, the same
  evening), `BufferedStream`'s changes (015-83, 019-02, 015-80,
  019-10) and the night's concurrency fixes that R7 reads.


## 2. How it runs

`java/stress/jcstress/run.sh JCSTRESS_DIR default JAR` from `java/`
(jcstress 0.16, its jars as in 016-08, section 4.1): it compiles the
tests against the jar, runs jcstress with `-m default`, and prints each
test's outcomes summed over its configurations. Not in `build.sh`, nor in
`before-commit.sh` or `night.sh`: a tool, run by hand.

The tests compiled against `main`'s jar (`e446bb2`) unchanged; no test
code changed.


## 3. s1: the results

2026-11-06, 11:50:28 to 12:16:16 (26 minutes), s1 (x86, 2 CPUs, idle
before the run, no other JVM), JDK 27, jcstress 0.16, `run.sh` in default
mode on the jar of `e446bb2` (its SHA-1 checked on s1): exit 0, 272 runs
of the tests' configurations, "Failed tests: No matches", "Error tests: No
matches". Output, with the JDK's warnings on JNA's native access left out:
[s1-default.txt](08-harness-concurrency/s1-default.txt).

| Test | Samples | FORBIDDEN seen | ACCEPTABLE_INTERESTING seen |
|---|---|---|---|
| HandlePublication          | 1,332,411,014 | 0             | 0 ("-1, 7")            |
| InstallPublication         |   880,816,774 | 0             | none declared          |
| EvictionRace               | 1,284,190,854 | 0             | none declared          |
| ValuePublication           | 1,647,915,654 | 0             | none declared          |
| GrowthPublication          |   457,484,934 | 0             | 1,472,866 ("14, 1, 1") |
| SwizzleOrder               |   676,313,734 | 0             | none declared          |
| TopSwizzleOrder            |   851,980,934 | 0             | none declared          |
| PlainPublication (control) | 6,892,495,494 | none declared | 0 ("0", the race)      |

* Each test `[OK]`.
* `GrowthPublication`'s interesting outcome is the reader's view between
  the growth's new array and its new size: the old size with the new
  array, which holds the copies (015-12's fix); allowed.
* `SwizzleOrder` and `TopSwizzleOrder` saw "0, 1" (the raise seen before
  the swizzle) 4.4 and 4.5 million times, allowed; never "1, 2", which
  F53 showed on the code before 015-14's fix.
* The control saw no race, as on s1 before (009-03, section 2): x86 keeps
  stores in order, so on s1 a pass shows little; F53's run is the one
  that counts.
* s1's files (`/opt/bergdb-bench/018-08/`) removed after the run.


## 4. F53: prepared, scheduled for the night

F53 was busy with other agents' gates on 2026-11-06, and jcstress fills
every core. Coord-1106's chain for the night (`chain.sh` of 006-13) runs,
after `night.sh large` (from 20:45, about 6 hours), the script
`/Users/f/fl/bench/006-13/night/jcstress-f53.sh` if it exists; a copy is
[08-harness-concurrency/jcstress-f53.sh](08-harness-concurrency/jcstress-f53.sh).
It:

1. waits, up to 20 minutes, while a QUIET-BLOCK marker other than q1's
   exists, then skips (q1's block waits for this run by its quiet check);
2. clones the main tree's committed `HEAD` and builds the jar;
3. runs `run.sh` in default mode with JDK 27 and 016-08's jars, under a
   limit of 40 minutes;
4. writes `/Users/f/fl/bench/006-13/night/jcstress-f53/` (`out.txt`,
   `results.txt`, `summary.txt`) and ends with a one-line summary,
   `JCSTRESS F53 OK`, `FAILED`, `ERROR` or `SKIPPED`.

The command, by the chain or by hand:

```
sh /Users/f/fl/bench/006-13/night/jcstress-f53.sh \
  > /Users/f/fl/bench/006-13/night/jcstress-f53.out 2>&1
```

Expected length: 5 to 10 minutes, and a minute for the clone and the
build (the five tests of 009 took 3.5 minutes on F53 on 2026-11-03,
016-08's F1, and 16 minutes on s1, where the eight took 26). Smoke test,
2026-11-06, 12:17: `SMOKE=1` (sanity mode, `PlainPublication` only, 2
CPUs) on `f0a47f3`, "JCSTRESS F53 OK: 1 tests [OK]", under a minute.

Check: every test `[OK]`; `PlainPublication`'s outcome "0" above zero (the
race seen, so the harness can see one on F53). A FORBIDDEN outcome is a
fault: verify it by jcstress's count, register it in 019, and write it up
here.


## 5. Log

2026-11-06. Created. The eight tests compiled against `main`'s jar
(`e446bb2`) unchanged; run on s1 in default mode (section 3); the F53 run
prepared for the night's chain (section 4). Each `[OK]` on s1, no
FORBIDDEN outcome. No test added: review R7 of 006-13 flags no shared
field that needs one. Run by Claude (Opus 5.5, Claude Code), agent j66 of
coord-1106.
