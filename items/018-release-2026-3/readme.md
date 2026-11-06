018-release-2026-3
==================

Created 2026-11-05 by Frans Lundberg. Status: open.

Release 2026.3 of BergDB: a bug-free Core, with no known issue at the
release but in DbObject and user indexes, which are experimental. The
plan, its decisions and the work towards the release.


Files
=====

* [01-plan.md](01-plan.md). 018-01, the plan:
  * the goal, in Frans's words: what the Core is (the Core Layer and the
    Pub API, but DbObject and user indexes), and when 2026.3 is ready;
  * the rules: 010's principles hold, and Frans approves any change of
    the stream format;
  * the Core's 54 known faults (52 entries of 015, S2-F24 and 014-01),
    and what is outside the goal;
  * the strategy proposed on 2026-11-05 and Frans's decisions D1 to D7;
  * his exceptions (none yet);
  * the harnesses by fault class, proposed;
  * the work W1 to W5.
* [02-harness-stream-contract.md](02-harness-stream-contract.md). 018-02,
  harness 6.3, the stream contract, built: a strict `AppendOnlyStream`
  for tests, a contract tester that every implementation passes,
  `BufferedStream` and `StorageManager` on the strict stream; it fails on
  the six known faults of its class and found 019-02; its skip list, where
  it runs (the unit tests, 0.6 s; the night tests, 20 s), what it does not
  cover.
* [03-harness-storage-faults.md](03-harness-storage-faults.md). 018-03,
  harness 6.2, failures and interrupts in storage, built: a fault (an
  `IOException`, an unchecked exception, an `Error`, an interrupt, a
  `stop()`) at every call of the stream and of the file calls under
  `FileStream`, in a short workload, with P7, the close, the lock, the
  threads and a restart checked after each run; it fails on 015-32, 35,
  53, 78 and 019-09, each before its fix, and found 019-10; where it runs
  (the unit tests, a sample, about 4 s; the night tests, 3.5 minutes).
* [04-harness-pub-promises.md](04-harness-pub-promises.md). 018-04,
  harness 6.7, the Pub API's promises, built: random sequences of the Pub
  API's calls on `String` and `byte[]` values against a reference of each
  key's versions by time; it fails on the six known faults of its class
  and found 019-15; five questions for Frans; where it runs (the unit
  tests, 1 s; the night tests, 80 s).


Log
===

2026-11-05. Created the item, at Frans's request ("Create item
nnn-release-2026-3 with this plan for working towards 2026.3."), with the
plan in 018-01. Claude (Opus 5.5, Claude Code) proposed the strategy that
morning, and Frans answered it at 09:28. Nothing started.

2026-11-05. 018-01 updated with Frans's answers of 09:43 (D4 to D7: the
rest of the Pub API in the goal, the limits not known issues, the
experimental methods, when the release is ready) and his rules (010's
principles; the stream format).

2026-11-05. 018-02: harness 6.3, the stream contract, built (W2), the
first harness, as Frans chose at 10:27. It fails on 015-26, 31, 33, 79, 80
and 83, each failure named by its entry, and found a seventh fault,
019-02; with its skip list of the seven it passes, in the unit tests of
`before-commit.sh` and in the night tests. BEFORE COMMIT OK.

2026-11-05, night 006-12. 018-04: harness 6.7, the Pub API's promises,
built (W2). It fails on 015-41, 42, 47, 48, 59 and 62, each with its fix
reverted, and found 019-15 (a delete under key replace), registered for
Frans's decision and in its skip list; five questions for Frans on the
Javadoc. In the unit tests of `before-commit.sh` (1 s) and the night
tests (80 s).

2026-11-06, night 006-12. 018-03: harness 6.2, failures and interrupts in
storage, built (W2). It fails on 015-32, 35, 53, 78 and 019-09, each on
the code before its fix, and found 019-10 (an unchecked read failure
leaves the database going on), registered and in its skip list; 015-06's
rest, 34, 38, 66, 81 and 82 it does not reach (018-03, section 6). In the
unit tests of `before-commit.sh` (a sample) and the night tests (every
file call, every 5th stream call). 019-10 fixed the same night.
