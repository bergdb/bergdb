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
* [05-harness-eviction-accounting.md](05-harness-eviction-accounting.md).
  018-05, harness 6.5, eviction's accounting, built: random budgets,
  test-schedule evictions, readers and restarts, with the audit, a
  recount of the resident bytes, the batches' handle limit and budget
  decreases checked after each batch; it fails on the five known faults
  of its class and found 019-20, 019-21 and 019-22; where it runs (the
  unit tests, about 1 s; the night tests, under 2 minutes).
* [06-harness-sizes-and-times.md](06-harness-sizes-and-times.md).
  018-06, harness 6.4, sizes and times at their limits, built: random
  transactions of the Core Layer at the value limit, the index nodes'
  bound, the last database times and top node ordinals, and the setters
  at their bounds, with reclaim, eviction and restarts; it fails on the
  three known faults of its class, found no new one; where it runs (the
  unit tests, 2 s; the night tests, 97 s).
* [07-harness-corrupt-streams.md](07-harness-corrupt-streams.md).
  018-07, harness 6.1, corrupt streams at a start, built: copies of
  streams written by `Db`, cut at every byte (the crash contract, a hard
  requirement) and damaged otherwise (best effort); it fails on the five
  known faults of its class and found 019-30 to 019-34 (019-34 fixed;
  019-30, 019-31 and 019-33 decided outside the fault model on
  2026-11-06 and counted as known; 019-32 in its skip list); where it
  runs (the unit tests, a sample, 3 s; the night tests, the full set,
  64 s).


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

2026-11-06. 018-05: harness 6.5, eviction's accounting, built in night
006-12 (W2). It fails on 015-67 to 015-71 with their fixes taken out, and
found 019-20, 019-21 and 019-22, fixed the same night. BEFORE COMMIT OK,
LEVEL 4 OK.

2026-11-06, night 006-12. 018-07: harness 6.1, corrupt streams at a
start, built (W2). Every truncation of its streams starts with exactly
its committed transactions; it fails on 005-74, 005-75, 015-07, 015-72
and 015-75, each with its fix reverted, and found 019-30 to 019-34,
in its skip list (019-32 to fix, 019-34 fixed that night, the others
for Frans).

2026-11-06, night 006-12. 018-06: harness 6.4, sizes and times at their
limits, built (W2). It fails on 015-50 and 015-55, each with its fix
reverted, and on 015-76 with the old Javadoc's promise as its oracle; no
new fault. In the unit tests of `before-commit.sh` (2 s) and the
night tests (97 s).
