016-release-2026-2
==================

Created 2026-11-03 by Frans Lundberg. Status: open.

Release 2026.2 of BergDB: its scope, the work before it, and how it is
made. The first release with handles (009) and bounded startup (007),
made as 2026.1 was (008), and measured against 2026.1 in turns.


Files
=====

* [01-plan.md](01-plan.md). 016-01, the plan:
  * the goal, and where `main` stands against 2026.1's known issues;
  * the rules for the work: the stream format kept unless Frans approves
    a change, replication and 014-01 out, doubles only at an API;
  * every unsolved issue known on 2026-11-03, each with a proposal: to
    fix before the release, a known issue of 2026.2, or not for 2026.2;
  * the work W1 to W7, and the search for unknown faults (H1 to H5);
  * the unattended run by one coordinator session;
  * Frans's decisions D1 to D7, and questions Q1 to Q4 for the start,
    with his answers.
* [02-run.md](02-run.md). 016-02, the run: the request, the subitems and
  agents, the timeline, the progress, the stops for Frans and the outcome.
* [03-notes.md](03-notes.md). 016-03, W1 and W2: the release notes from
  `releases/next.md` and the walk of `git log release-2026.1..`, and
  2026.1's post-release notes.
* [04-documents.md](04-documents.md). 016-04, W3 and replication's
  wording: the Javadoc, README.md, docs/levels.md and lean/README.md.
* [05-fixes.md](05-fixes.md). 016-05, W4 and H5: the fixes before the
  release, their order, gates, reviews and hand-off; the quiet block's
  steps.
* [06-reviews.md](06-reviews.md). 016-06, H1 and H2: the reviews of the
  changes since 2026.1 and of the Pub API's promises; the reports in
  `06-reviews/`.
* [07-concurrency.md](07-concurrency.md). 016-07, H3: the threads, locks
  and shared fields, and the jcstress tests to add.
* [08-tests.md](08-tests.md). 016-08, H4: the tests beyond the gates,
  Linux, JDK 17, jcstress, the stress programs; scripts in `08-tests/`.
* [09-release.md](09-release.md). 016-09, W6: the release by 008-01's
  steps, commits A and B, the files, the tests on the jar.
* [10-numbers.md](10-numbers.md). 016-10, W7: the numbers against 2026.1,
  in turns, in the quiet block.


Log
===

2026-11-03. Created the item, at Frans's request ("Create bergdb item
016-release-2026-2. This is for planning the 2026-2 release. The scope of
it and the work needed."), with the plan in 016-01. Nothing done yet; the plan waits for Frans's
decisions (016-01, section 8).

2026-11-03. 016-01 reviewed and revised, at Frans's request (15:01, "Now,
review your plan. You now have Max effort level."), with his decisions D1
to D6 (016-01, section 10):

* The issue list was made from every open 005 entry, 014, 015, 007,
  010-01's "To check" lines, docs/levels.md's limits, 012's findings in
  Java and 009's leftovers.
* Added: 005-79, 005-65's rerun, the search for unknown faults, and the
  unattended run.
* Corrected from the draft: `night.sh` OK since 2026-10-30; 005-76 does
  not change what the C clone compares; 005-50 added to 2026.1's faults.
* Found: 005-82's log has Frans's earlier question about crash tails
  (now Q1); no JDK 17 on F53 or s1; no record of the gates on Linux or of
  a large conformance run with handles; a directory without its stream
  files starts as a new database (Q4).

Four questions wait for Frans before the start (016-01, section 11).
Nothing done yet.

2026-11-03, 15:27. Frans answered Q1 to Q4 and started the coordinator
(013-02), unattended until 07:00; at 15:31 he limited the release to Java
(D7). Both are in 016-01, section 10. The run is 016-02. The detailed
plans are being written as 016-03 to 016-10, and in the entries of W4.

2026-11-04. Release 2026.2 made: commit A `95bde62` (BuildInfo 2026.2), the
tag `release-2026.2` on it, and commit B with `releases/2026.2/` and
BuildInfo 2026.3-dev. The night's session stopped from 22:20 to 07:24 (a
refused OAuth refresh; docs/log.md), so the release steps ran in the
morning. 22 entries were closed for it (5 of 005, 17 of 015, two of them
fixes of tests), and the reviews registered their other faults as 015
entries (known issues in the notes). The W7 numbers follow from night
2's quiet block (016-10). The run and its outcome: 016-02.
