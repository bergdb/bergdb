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
  Linux on record.
* **L2, JDK 17, `6f932f0`**: `before-commit.sh`: `BEFORE COMMIT OK (147
  s)` (16:08 to 16:11).
* **`level1.sh` on s1: does not fit the machine.** It failed twice
  (16:06, and 16:20 with its RestartStress JVMs one after another, in s1's
  copy only): the OOM killer took its JVMs (`dmesg`: "Out of memory:
  Killed process ... (java)", 16:03 and three at 16:17). Its steps start
  several `-Xmx2g` JVMs at once, and s1 has 3 GB and 2 cores. An
  environment limit, not a fault (section 2, "A failure"); not run again.
  The stress programs run on s1 in L4 with `-Xmx1g` and two lanes.
* **The night tests on s1, first runs**: FAILED on JDK 27 (16:08) and 17
  (16:13), each only in `BryanIssueNight`, with "No space left on device":
  the tests' `TempDirCreator` writes to `/tmp`, hard-coded, and s1's `/tmp`
  is a 1.9 GB tmpfs; `-Djava.io.tmpdir` does not move it (the retry at
  16:23 and 16:25 failed the same way). An environment limit. Rerun from
  16:31 with `/tmp` bound to a directory on the disk in a private mount
  namespace (`unshare -m`, the run's processes only;
  `/opt/bergdb-bench/016/h4/run-night-ns.sh`).
* **The night tests on s1, with `/tmp` on the disk, `6f932f0`**: JDK 27
  "SUCCESS, 8 successful tests in 183.4 s" (16:31 to 16:34); JDK 17
  "SUCCESS, 8 successful tests in 190.8 s" (16:34 to 16:38). The first
  night tests on Linux on record.
* **015-10's check**, full `bergdb.dev.Unit` on s1, JDK 27, the base's jar
  (`6f932f0`) and main's (`3e32f02`) in turns, three rounds, the first two
  beside the night tests: six of six SUCCESS (1,093 and 1,101 tests);
  `CapacityTester.testBudgetLoweredAndRaisedUnderReads` passed each time.
* **L3, jcstress, default mode, `3e32f02`, JDK 27** (16:44 to 17:00, with
  `/tmp` on the disk): the five tests `[OK]`; "Failed tests: No matches",
  "Error tests: No matches". L4, the stress programs on disk, runs until
  23:30.
