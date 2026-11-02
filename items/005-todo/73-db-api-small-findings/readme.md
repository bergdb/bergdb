005-73 validation, 2026-11-02
============================

Baseline: `0e61856475ab1392ef64ed2ef5f9289ad54e6140`.

* `regressions-before.txt`: the three new `DbTester` regressions run
  against an archived baseline, with only the test source copied in.
  All three fail. The fourth counted test is the runner's own check.
* `regressions-after.txt`: the same three regressions pass with the fix.
* `digests-before.txt` and `digests-after.txt`: all 12 StreamDigest
  configurations in plain, reads and restarts modes. The same baseline
  StreamDigest classes ran against both jars.
* `digests-compare.txt`: all 36 digests identical.
* `before-commit.txt`, `unit.txt` and `f.txt`: BEFORE COMMIT OK,
  1,090 unit tests and 78 f-tests, including F4.

The focused regression command, after building with `java/build.sh`:

```sh
java -ea -cp java/build/bergdb.jar bergdb.dev.Unit \
  -c bergdb.core.DbTester \
  -m 'testStartInfoReportsEffectiveDistance|testCloseReportsFinalFlushFailure|testCloseFailureSuppressedByBlockFailure'
```

No level mechanism changed. The required validation is
`java/before-commit.sh`; the stream comparison checks the claim that
these API and monitoring changes do not change stored bytes.
F4's additional regression is recorded in `f4-before.txt` (fails on NaN)
and `f4-after.txt` (passes). The double API and C clone are unchanged;
005-79 is separate.
