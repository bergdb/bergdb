Notes for the next release
==========================

What the release notes of the next release after 2026.5 must say, collected
here as the changes are made, so that the release does not have to find them
again. The release folds them into its `releases/VERSION/readme.md`, as
[2026.5](2026.5/readme.md) has them under its changes, and
empties this file. A change of the stream's bytes, within the format,
names the StreamDigest configurations whose digests changed and the entry
that keeps its digests before and after (bergdb 018-01, section 2).

Emptied at release 2026.5 (2026-11-13), whose notes hold what was there.


### Core API

* **A value transformation that throws or passes 8 MiB refuses its
  transaction; the database goes on** (bergdb 026-06; 010-04, R5; Frans,
  2026-11-12, 14:42). A user transaction's value transformations now
  run in `Db.execute()` under the write lock, after the key
  transformations and before the go point, in key order, each with the
  value as given and the key's value before the transaction, as before.
  A `RuntimeException` from one, a result over 8 MiB (L4), or results
  that take the transaction over 32 MiB of keys and values (L5) refuse
  the transaction with a `DbException` (the exception as its cause):
  nothing is written, and the `Trans` is left as it was, its values as
  given, its keys as written, its time given back, so it can be run
  again. In 2026.5 each failed the database (2026.5's Known issues;
  024-24, QL6; 015-51). An `Error` still fails it. **A key
  transformation that throws** a `RuntimeException` is refused in the
  same way (026-06, D9). No stream change. Tests whose expected values
  changed: `DbTesterLimits.testTransformedValueOverL4`,
  `DbTester.testTransformedValueBeyondRecordLimit`, `LimitsTester` (a
  result above the value limit refused, no run ends by the caller's
  fault), and three of `DbTesterFailure` that now fail after the go
  point by a test hook.
