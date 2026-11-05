# 006-12 Unattended work, 5 to 6 November 2026

Created 2026-11-05 by Frans Lundberg. Status: in progress (since 14:38). The
plan for the unattended work from 2026-11-05, 15:00, to 2026-11-06,
07:00, the progress through the night, and the outcome. The way of
working is 013-01's (the night) and 013-02's (the coordinator), as in
006-10.


## 1. The request

Frans, 2026-11-05, 08:52: "We will work interactively today. I expect a
lot of work. Let's plan unattended work for tonight. Preliminary from
15:00 to 07:00 using a coordinator session. [...] create an item in 006
for this night plan. Similar to 006-10."

F53 is Frans's for interactive work until 15:00. Nothing of this plan
loads it before then; the day's preparation is reading and writing only.

**To answer before 15:00** (each with a recommendation; if a question has
no answer when Frans leaves, the recommendation stands, as agreed on
2026-11-05: "leaving soon" means the questions are asked at once, and
the work does not wait for the answers):

1. **The lead session.** Recommended: a new coordinator session,
   coord-1105, which Frans starts in the afternoon with `/coordinator
   start`, tells to read this plan, and switches to unattended at 15:00
   (`/coordinator unattended`). It owns the night's commits, item numbers
   and heavy runs. The session "Open items in 005", which closed 005 this
   morning, has a long context and nothing left open, so it does not lead.
2. **W1, the 015 fixes.** Recommended: as many of the open Fix entries of
   015 as the night allows, in the order of section 3 (the stream's
   integrity first), each with a regression test that fails before and
   passes after, `before-commit.sh`, and the level script of any level
   whose mechanism it changes. Committed in Frans's name, one fix or one
   small group a commit.
3. **W2, the two quiet blocks on F53.** Recommended: Q-A, 22:30 to about
   23:45, 015-86's measurements (the ones Frans decided); Q-B, 05:00 to
   06:15, a performance check of the night's `java/` changes against
   15:00's `main`.
4. **W3, 015-88 on s1.** Recommended: the retry variants R0 to R2 as
   patches, measured on s1, and an `executeRw()` proposal written for
   Frans; no change to `java/`.
5. **Decisions that would add work.** If Frans answers 015-87's F1 to F7
   during the day, its change (U6) joins W1 after the stream fixes.
   015-05 and 015-27 (Decide) likewise. Otherwise they stay for him.

Frans's answers, 2026-11-05, 09:02:

1. "Yes, as proposed. I will call it coord-1105 and start it in the
   afternoon."
2. "Yes, as the current plan."
3. "Yes, as the current plan."
4. "W3, I need to look at this." Open: W3 waits for Frans; without his
   word by 15:00 it does not run tonight. Dropped for tonight by Frans's
   decision of 14:12 on 015-88: the retry variants and the `executeRw()`
   proposal moved to 017-06 (section 3, W3).
5. "To be done during the day." The decisions are Frans's during the day;
   the change of any that he decides joins W1.

Frans, 2026-11-05, 10:18, to session bergdb-e8, after 018 was created
(09:28 to 09:50): "Yes, do as you suggest." The night works on 018-01's
goal list and leaves the experimental code alone; W1 in section 3 says
how.


## 2. Ground rules

013-01, section 4, and 013-02, with these for tonight:

* **Effort and agents.** At most 4 subagents at a time, each at high
  effort; the coordinator at xhigh, the default of a new session, and it
  does little work itself (Frans, 2026-11-05, 12:04: "Let's run agents at
  High tonight. Coordinator at XHigh, though."). An entry that needs a
  concurrency or safety argument, such as 015-80 (the buffer's concurrent
  writes), or whose gate fails twice at high, is written up and skipped:
  it waits for a day session at xhigh and is not retried at xhigh tonight.
* **The weekly ceiling, 80 %** (Frans, 12:04). The coordinator reads
  `usage.sh` before every agent it starts and at every check-in, and
  starts no agent once the week is at 80 % or more; a running agent
  finishes its entry, hands it over if its gate passes, and stops. The
  rest, to the reset on Monday 9 November at 22:00, is the day work's.
  Tonight the ceiling takes the place of the week's tests in 013-02's
  levels (85 %, or 25 points ahead of its time); the 5-hour window's tests
  stay (tight at 80 %: at most two agents; limit at 98 %: none until the
  reset).
* **Clones.** Each agent works in its own scratch clone under
  `/Users/f/fl/bench/006-12/`, gates there, and hands its change to the
  coordinator, which lands one change at a time on `main`: rebase,
  `before-commit.sh` on the combined tree, commit. Two agents' commits
  swept each other's staged files on 2026-11-05; only the coordinator
  commits `java/`, and every commit stages its paths by name.
* **Authorship.** Commits in Frans's name, with no Co-Authored-By or other
  AI attribution; documents "Created ... by Frans Lundberg".
* **The stream's bytes.** No fix changes the bytes of a database that
  was valid before it, unless Frans approves (016-01, section 3); a fix
  that would is stopped and written up for him. The C clone (012, 015-02)
  follows later; bergdb-2c owns 015-02.
* **Quiet blocks.** The marker `/Users/f/fl/bench/quiet-block-*/QUIET-BLOCK`
  (bergdb-2c checks for it, 2026-11-05) and the coordinator's own marker;
  no builds, gates or tests on F53 while it exists. macOS's
  `mediaanalysisd` may be paused with `kill -STOP` during a block and is
  resumed after it, with a safety (Frans, 2026-11-05, 07:32); each pause
  is logged in the block's directory.
* **`night.sh`** stays at 02:10, on a clone of the committed code; no
  gates run from 02:05 to its end (about 02:50).
* **Other sessions.** bergdb-2c works on 015-02 (the C clone) and runs
  `cross.sh` on F53; it is told the night's quiet blocks. Frans's own
  sessions of the day report to the coordinator what they leave running.
* **News.** `tools/news.sh` as work finishes, fails or needs Frans; the
  summary by 07:00 on 2026-11-06.


## 3. The work, in order

### W1. 015's open fixes

The Fix entries of 015, most from release 2026.2's reviews (016-06),
grouped by area so that agents in parallel touch different code. Each
group is one agent's queue, in this order within it. The coordinator
reads each entry first: an entry that turns out to need a decision, a
format change or more than a few hours is written up and skipped.

The night follows release 2026.3's goal (018-01, section 1): it fixes the
Core's known faults (018-01, section 3.1) and leaves the entries of the
experimental code, DbObject and user indexes (018-01, D2 and D6), alone.
An entry that the day's session, bergdb-e8, has marked `in progress` or
`done` in its file is skipped.

1. **The stream and its storage** (the integrity of what is written and
   read back):
   * a start's checks: 015-72 (a record's size larger than its content),
     015-73 (a corrupt startupPos), 015-75 (checks that are asserts);
   * appends: 015-26 and 015-79 (a negative append length), 015-80 (the
     buffer's concurrent writes), 015-33 (`setMax2G`);
   * failures and stops: 015-35 (a failed background write), 015-81 and
     015-78 (close errors), 015-34 (an interrupt at the stop), 015-32 (a
     failed open);
   * cuts and reads: 015-82 (a pending cut), 015-31 (a cut at the
     length), 015-83 (a read past the end);
   * 019's: 019-01 (a meta block's version read as 2 bytes), 019-02
     (the streams' refusals of a bad length).

   Harness 6.3 (018-02, built 2026-11-05) is the failing test of 015-26,
   31, 33, 79, 80, 83 and 019-02: each fix deletes its own line in
   `StreamContract.SKIP`, and a line left after its fix fails the unit
   tests.
2. **Eviction and the capacity controller:** 015-66, 015-67, 015-68,
   015-69, 015-70, 015-71. `level4.sh` before landing.
3. **Transactions, reclaim and time:** 015-50, 015-51, 015-52, 015-53,
   015-55, 015-57, 015-58, 015-63, 015-64; the comments and Javadoc
   015-54, 015-74, 015-76, 015-77. `level3.sh` for a change to reclaim.
4. **The Pub API, the Core's part** (018-01, D4): 015-38, 015-41,
   015-42, 015-44, 015-45, 015-47, 015-48, 015-59, 015-60, 015-62,
   015-65, and S2-F24 of 015-49 (keys with a lone surrogate).
5. **Tools and tests:** 015-04, 015-08, 015-11, 015-19.

Groups 1 and 2 start at 15:00, 3 and 4 when an agent is free; 5 fills
gaps. 015-06 is in progress elsewhere and is left alone. Not every entry
will be done tonight; the morning's Outcome lists what was.

### W2. The quiet blocks on F53

* **Q-A, 22:30 to about 23:45: 015-86's measurements.** Frans decided on
  2026-11-05: as the AB/BA step showed that the rise of the gets over 10 ms
  is the fix's (`988fe1a`), "take the measurements and move the decision
  to 015". The Recommendation's three: `threads.sh` with 7 threads; with 8
  threads and `-XX:ConcGCThreads=1`; and the get's parts timed in
  ScaleBench (a change to `ScaleBench-065.diff`, made and smoke-tested in
  the afternoon, using little CPU). Both builds as in the AB/BA step. The
  results and the explanation go into 015-86 for Frans's decision.
* **Q-B, 05:00 to 06:15: the night's performance check.** `performance.sh
  ab` with the quick suite: `main` at 15:00 against `main` at 05:00,
  ABBA. No scenario may lose more than its CV; a loss is traced to its
  commit and written up for Frans, not reverted.
* **Q-W7, after Q-A, from about 23:45 to 01:20: release 2026.2's
  numbers** (016-10; 016-02, "Open for the next coordinator", item 1).
  Added at Frans's word, 2026-11-05, 10:34: the night of 4 to 5 November
  ran none of W7's five F53 steps, as their `lib.sh` had a fixed deadline,
  night 1's 2026-11-04 06:05; since 10:40 it requires `DEADLINE`. A shell
  process started at 10:43, independent of any session, runs the block:
  `/Users/f/fl/bench/016/night3/block.sh` (pid in `pid`, its rules in its
  header). At 23:40 it writes its marker
  `/Users/f/fl/bench/quiet-block-2026-11-05-w7/QUIET-BLOCK`, so W1 does
  not resume after Q-A; when no other marker (Q-A's) and no JVM, gate or
  Lean is left, it pauses `mediaanalysisd`, waits for a load below 1.5
  (until 00:15 at the latest), and runs props, sb-m, sb-c, pp and quick-ab
  (8, 22, 32, 10 and 22 minutes; none that would end after 02:05). Then it
  removes the marker, resumes `mediaanalysisd` and writes `news.md`. The
  coordinator: Q-A's own marker stays until Q-A's last run ends (the block
  waits for it), and W1 resumes when the W7 marker is gone. To stop it or
  to move it: `kill $(cat /Users/f/fl/bench/016/night3/pid)`, then start
  it again with `START`, `LATEST` and `DEADLINE` (epochs) as its header
  says. In the morning, not tonight's work: `collect.sh` with
  `C=/Users/f/fl/bench/016/night3` and the commit of 016-02's item 1.

### W3. 015-88 on s1

The retry variants R0 to R2 of 015-88, section 4, as patches in the style
of `make-probe.py`, measured on s1 (2 vCPUs) with the harness of
2026-11-05 on the hot-key, disjoint-key and history cases; then a concrete
`executeRw()` proposal in the entry, for Frans. `ps` on s1 first.

Dropped for tonight by Frans's decision of 2026-11-05, 14:12, with
session bergdb-e8: 015-88 only caps the retry sleep at 640 ms for
release 2026.3 (a day change, by bergdb-e8's agent), and the retry
variants and the `executeRw()` proposal moved to 017-06, a long-term
topic, with his question whether `rw()` should ever give up under
overload. Nothing runs on s1 tonight for it.

### Not tonight

* Decisions: 015-05, 015-27, 015-87's F1 to F7 (unless answered by
  15:00), 015-88's sections 2.6 and 3.1 (017-06's since 14:12), and
  015-86's decision.
* 015-84, the cap of the pace's factor: about a day of F53 at the lowest
  priority, which tonight's gates would disturb. A later night.
* 015-02 (bergdb-2c), 015-03 (Lean), 015-18 (`night.sh large`, by hand).
* The experimental code's entries (018-01, section 3.2): 015-23, 015-28,
  015-29, 015-30, 015-36, 015-37, 015-39, 015-43, 015-46, 015-61, and
  015-49 but S2-F24.


## 4. The principles (010)

Each fix is checked against 010-01; a departure is written there. Across
all of it: no new setting (P10), no global state (P9), no new timer or
polling thread (P3), the simple fix first (P11), and the stream's bytes
the same (P2).


## 5. Timeline

Times in CET.

| Time | What |
|---|---|
| 09:00–14:45 | Frans works interactively; this plan, the questions; Q-A's ScaleBench change prepared without load |
| 14:45 | coord-1105 started, reads this plan; the check-ins scheduled (section 6) |
| 15:00–22:15 | W1 groups 1 and 2, then 3 and 4 |
| 22:15 | CPU-heavy work on F53 stops |
| 22:30–23:45 | Q-A, 015-86's measurements |
| 23:45–01:20 | Q-W7, release 2026.2's numbers (its own marker from 23:40; at the latest to 02:05) |
| 01:20–02:05 | W1 goes on |
| 02:10–02:50 | `night.sh` (launchd); no gates |
| 02:50–05:00 | W1 goes on; the last landing by 05:00 |
| 05:00–06:15 | Q-B, the performance check |
| 06:15–07:00 | The Outcome; the summary in `news.md` |


## 6. If the coordinator stops

As 013-02 and 013-01, section 6: the coordinator's check-ins and
watchdog (`/coordinator` sets them up), its `state.md` in
`/Users/f/fl/bench/coord/2026-11-05/`, this file's Progress section, and
each entry's State. A fresh session reads those and goes on.


## 7. Progress

Times from `date`, CET.

* 14:38 coord-1105 started (Frans: "You are my coordinator for the
  unattended work 006-12. Do the work as planned."; 14:42: "You are
  called coord-1105."). The day session bergdb-e8 handed over
  (`/Users/f/fl/bench/day-1105/handover.md`): 015-87 (U6) and 015-88 done
  in the day, W1's queue shorter, the day's gates under one lock, and
  Q-A's ScaleBench change not prepared. Its last commits, d0d408d and
  1068442, at 14:43; main at 15:00 is 1068442, Q-B's reference.
* 14:40 Last-minute questions to Frans, each with a default that goes
  ahead: (1) the session's name; (2) Q-A's ScaleBench change prepared by
  an agent in the afternoon, compiled only against the AB/BA builds'
  jars; without it by 21:45, Q-A runs the two `threads.sh` variants only;
  (3) Q-B as planned, reference 1068442; (4) W1 as one fresh agent per
  batch of 2 to 4 entries, 015-80 skipped. Answered: (1) coord-1105.
* 14:44 The night's tools in `/Users/f/fl/bench/006-12/`: `gate.sh` (every
  gate under the day's lock, `/Users/f/fl/bench/day-1105/gate.lock`, and
  refused in a quiet block or window: 22:15 to midnight, 02:05 to 02:55,
  04:58 to 06:20, or with a QUIET-BLOCK marker), `land.sh` (the
  coordinator's landing: cherry-pick onto main in a landing clone,
  `before-commit.sh` on the combined tree, `git merge --ff-only` in the
  main tree), `brief-w1.md` (the W1 agents' common brief). Started at
  high: W1 g1a (015-72, 73, 75), g2a (015-66, 67, 68), g3a (015-50, 51,
  52), and the preparation of Q-A and Q-B (scripts in `qa/` and `qb/`,
  smoke tests, started by 20:30). Check-ins every 20 minutes but 22:00 to
  00:59 and 05:00 to 05:59; a one-off at 21:53; the watchdog until 07:00.
  Usage at 14:43: 5h 29 %, week 45 % (ceiling 80 %).
* 15:00 to 15:59 W1's first batches landed, each with `before-commit.sh`
  on the combined tree: 015-72 (9a315e6) and 015-75 (eb9ab4b); 015-73
  skipped for Frans (8616162), then decided by him at 15:35 in session
  bergdb-a2, (a) outside the fault model for 2026.3 and a new 019-07 for
  a record header checksum at the next format change (49a814e); 015-50
  (bb3be64, StreamDigest 48 of 48 the same, LEVEL 3 OK), 015-51
  (8427ff0, Javadoc only, R7's first option: for Frans to confirm),
  015-52 (0b99498); 015-66 (578c263), 015-67 (4d706da), 015-68 (ec57528),
  LEVEL 4 OK; 015-26 and 015-79 (7a3d317), 015-33 (8ae7969), their lines
  gone from `StreamContract.SKIP`. Started: g1c (015-35, 81, 78, 34, 32),
  g2b (015-69, 70, 71), g3b (015-53, 55, 57, 58).
* 15:38 Q-A (pid 74282) and Q-B (pid 74284) ready and started, smoke
  tests OK; Q-A has all three measurements, the get's parts timed by
  `ScaleBench-086-parts.diff` on top of 065 (scripts and READMEs in
  `/Users/f/fl/bench/006-12/qa/` and `qb/`; a guard process removes each
  marker at its hard stop, 00:03 and 06:15).
* 15:45 to 15:50 Landings starved by the agents' gates (`lockf` serves no
  queue): landings first since then (`land-waiting`); a waiter of the
  coordinator's that matched itself in `pgrep -f` held the gates for five
  minutes.
* 16:00 to 17:06 W1 landed, each with `before-commit.sh` on the combined
  tree: 015-53 (fddaf1f), 015-55 (f679430), 015-57 and 015-58 (e24276a),
  LEVEL 3 OK; 015-35 and 015-81 (dc46c1e), 015-78 and 015-34 (1b66a34),
  015-32 (37ce61f); 015-63 (825e5b1), 015-76 (f5e73ea, Javadoc only, R6-F5's
  first option); 015-69 (27d1b07), 015-70 (611d9c5), 015-71 (70d8ec2),
  LEVEL 4 OK; 015-38 (bf80659), 015-41 (439ec79), 015-60 (3dea90a); 015-82
  (6b7f5b2), 015-31 (fc87e5c), 015-83 (d9b8dc5), harness 6.3's SKIP down to
  015-80 and 019-02; 015-65 and S2-F24 of 015-49 (to 95d52c3); 015-11,
  015-08, 015-04, and 015-19 but ScaleBench, which tonight's blocks use
  (to b6838e5). W1's groups 2 to 5 are done; group 1 has 019-01 and 019-02
  left (g1e, started 16:58) and 015-80, which waits for a day session.
* 17:01 Not in the plan, the coordinator's decision: two read-only review
  agents check tonight's fixes with fresh eyes (R1 the stream, its storage
  and the start; R2 eviction, transactions, reclaim and the Pub API), as
  about 30 fixes were made at high effort unattended and several touch
  concurrency. Findings in `/Users/f/fl/bench/006-12/review-r1.md` and
  `review-r2.md`, faults as 019 entries; they stop by 21:45.
* 17:13 W1's last batch landed: 019-01 (f95840e) and 019-02 (669f0ef);
  harness 6.3's SKIP is down to 015-80. W1 is done but 015-80, which
  waits for a day session.
* 17:14 to 17:51 The reviews. R1 (the stream, its storage, the start): 9
  of 10 commits OK; in dc46c1e (015-35, 015-81) a regression, B1, shown by
  a probe: `Db.close()` could return before a failed storage had closed
  its stream; fixed by 7a80d0d (`closeInner` closes the stream also after
  a failure; the close's failure kept as suppressed, C2), and R1's
  re-review found the fix right. That re-review found B2, older than
  tonight (2026.1 and 2026.2 have it): `close()` after a background write
  failure that no call met returns normally and reports nothing; it is
  019-09, waiting for Frans (112ab21). R2 (eviction, transactions,
  reclaim, the Pub API): all 19 commits OK, 23 of their 25 new tests fail
  without their fix (the other two pin documented behaviour); B1 outside
  the commits, the Core's `DbUtil.dbTimeToUtc` with 015-63's fault,
  registered and fixed as 019-08 (5a2e6d6); 015-60's Javadoc made exact
  and four long lines wrapped (7476107); and C1, 15 closed rows left in
  015's Open table by the coordinator's union merges, removed (57ad705;
  no union merge for the readmes since). R3 (019-01, 019-02 and group 5):
  all OK; 015-11 closed although the s1 half of its "Done when" was not
  run (for Frans).
* 17:48 On the combined main 669f0ef, all of W1: LEVEL 2 OK (70 traces,
  TRACECHECK OK), LEVEL 3 OK, LEVEL 4 OK. 17:56 the same again on
  112ab21, with the review fixes.


## 8. Outcome

(to be written by 07:00 on 2026-11-06)
