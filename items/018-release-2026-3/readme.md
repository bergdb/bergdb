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
