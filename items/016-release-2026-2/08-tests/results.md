016-08, results
===============

Created 2026-11-03 by Frans Lundberg.

The summaries of 016-08's runs (H4): the command, the commit, the seeds,
the pass line or the failure's first lines, the minutes. Raw outputs stay
outside the repository, in the run's directory. Times from `date`.


## F53

* **F1, jcstress, default mode, `6f932f0`** (16:02 to 16:05, 3.5
  minutes). `sh stress/jcstress/run.sh /Users/f/fl/bench/016/jcstress-lib
  default` in `/Users/f/fl/bench/016/h4-jcs/repo/java`, JDK 27. All five
  `[OK]`; "Failed tests: No matches", "Error tests: No matches". No
  forbidden outcome in `EvictionRace` (654,256,454 samples),
  `HandlePublication` (895,029,894), `InstallPublication` (728,640,134)
  and `ValuePublication` (1,100,976,774). The control `PlainPublication`
  saw its race 124,076 times in 3,604,308,614 samples, so the harness can
  see one on F53.
* **F2, JDK 17, `323a54a`** (16:05 to 16:09). In
  `/Users/f/fl/bench/016/h4-jdk17/repo/java`, with `JAVA_HOME` and the
  PATH at `/opt/homebrew/opt/openjdk@17` (java and javac 17.0.21.0.3):
  `before-commit.sh`: "Unit: SUCCESS, 1093 successful tests in 9.8 s",
  "F: SUCCESS, 78 successful tests in 71.0 s", `BEFORE COMMIT OK (76 s)`;
  `night.sh tests`: "SUCCESS, 8 successful tests in 143.1 s".


## s1

* **L1, JDK 27, `6f932f0`**: `before-commit.sh`: `BEFORE COMMIT OK (121
  s)` (15:59 to 16:01). The first run of the unit tests and the f-tests on
  Linux on record. `level1.sh` and the night tests follow.
