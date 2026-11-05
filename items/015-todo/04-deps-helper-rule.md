015-04. Investigate: deps.py counts TransSeq.take and dither as test code
=========================================================================

Status: done 2026-11-05, night 006-12. Kind: Investigate. Created 2026-11-03 by Frans Lundberg.

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

2026-11-05. Done in night 006-12.

Answers. The rule is wrong, not only its name: it looked at one file. A
method or nested class whose name the file uses only in test code counted
as a helper of the tests, also when other files call it from production
code. So `TransSeq.take`, which `Db` calls, was test code, and with it
`ditherFp`, `shareFp` and the rest of what only `take` calls in
`TransSeq.java`. Over `java/src` the rule found 427 helper declarations;
319 of them are production code by the corrected rule: much of the public
API of `BufferedStream`, `RecoverableStream`, `MetaBlock`, `Bytes`,
`TimeResolver`, the streams, `Reclaim`'s getters and so on, called from
other files. The list, by package, class and name:
[04-deps-helper-rule/misclassified.txt](04-deps-helper-rule/misclassified.txt),
made with `compare-rules.py` beside it.

It did not change `deps.py`'s verdict: a package's list in `package.html`
covers production and test code alike, so only the printout's split
("production code uses" or "test code only uses") could be wrong. On
today's tree the corrected rule prints the same as the old one.
005-79's `doubles.py` uses `test_regions(..., helpers=False)` and so never
had the fault.

Fix (`java/deps.py`): `scan` first collects the words of each file's
production code by the direct markers (Tester files and classes, `@Nano`,
`test...` methods; `production_words`), and the helper rule skips a
declaration whose name another file's production code uses
(`test_regions`'s new argument `used_elsewhere`). It compares names, not
declarations, so a real helper whose name another file also uses in
production code (`read`, `close`) counts as production code: the safe
side, as the check takes both alike. The docstring says so. 108 helpers
are left, such as `FileStream.Run` and `MemoryStream.checkCopy`.
`doubles.py`'s comment on the rule is updated; it keeps `helpers=False`.
`deps.py` takes about 1.2 s instead of 1.0 s.

* Check: `test_regions` on `TransSeq.java` puts `take`, `ditherFp` and
  `shareFp` in test code before the fix and in production code after it.
  `python3 -I java/deps.py` prints the same as before the fix
  (`diff`), "9 packages, all as package.html allows"; `compare-rules.py`
  gives the list.
* 010-01: a tool; no setting; the stream's bytes unchanged.
