# 006-12 Unattended work, 5 to 6 November 2026

Created 2026-11-05 by Frans Lundberg. Status: planned (preliminary). The
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
   word by 15:00 it does not run tonight.
5. "To be done during the day." The decisions are Frans's during the day;
   the change of any that he decides joins W1.


## 2. Ground rules

013-01, section 4, and 013-02, with these for tonight:

* **Effort and agents.** At most 4 subagents at a time, each at xhigh
  effort (high only if usage is tight); the coordinator does little work
  itself.
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
     length), 015-83 (a read past the end).
2. **Eviction and the capacity controller:** 015-66, 015-67, 015-68,
   015-69, 015-70, 015-71. `level4.sh` before landing.
3. **Transactions, reclaim and time:** 015-50, 015-51, 015-52, 015-53,
   015-55, 015-57, 015-58, 015-63, 015-64; the comments and Javadoc
   015-54, 015-74, 015-76, 015-77. `level3.sh` for a change to reclaim.
4. **The Pub API and the indexes:** 015-23, 015-28, 015-29, 015-30,
   015-36, 015-37, 015-38, 015-39, 015-41 to 015-48, 015-49 (review S2's
   faults), 015-59 to 015-62, 015-65.
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

### W3. 015-88 on s1

The retry variants R0 to R2 of 015-88, section 4, as patches in the style
of `make-probe.py`, measured on s1 (2 vCPUs) with the harness of
2026-11-05 on the hot-key, disjoint-key and history cases; then a concrete
`executeRw()` proposal in the entry, for Frans. `ps` on s1 first.

### Not tonight

* Decisions: 015-05, 015-27, 015-87's F1 to F7 (unless answered by
  15:00), 015-88's sections 2.6 and 3.1, and 015-86's decision.
* 015-84, the cap of the pace's factor: about a day of F53 at the lowest
  priority, which tonight's gates would disturb. A later night.
* 015-02 (bergdb-2c), 015-03 (Lean), 015-18 (`night.sh large`, by hand).


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
| 15:00–22:15 | W1 groups 1 and 2, then 3 and 4; W3 on s1 |
| 22:15 | CPU-heavy work on F53 stops |
| 22:30–23:45 | Q-A, 015-86's measurements |
| 23:45–02:05 | W1 goes on |
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

(to be written through the night)


## 8. Outcome

(to be written by 07:00 on 2026-11-06)
