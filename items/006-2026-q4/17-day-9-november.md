# 006-17 Day work, 9 November 2026

Created 2026-11-09 by Frans Lundberg. Status: open. The plan for the
coordinator's day of 2026-11-09 (coord-1109), a Monday: the last work on
release 2026.4 (020) before its cut, the progress and the outcome. The
way of working is 013-02's (the coordinator).


## 1. The request

coord-1108's handover (006-15, section 6.5): integrate 020-13's fixes
and 006-16's item when coord-1108 sends them; a Codex review of 2026.4's
riskiest code; the release candidate after 020-13 (and Codex, if Frans
wants to wait for it). Frans, 2026-11-09, 08:41 (to coord-1108): "I want
the test study before the release cut. This release focus is 'bug-free
database'."

Frans, 09:11: "Codex command line is installed, let it do the code
review. Use latest Sol, effort Max." (020-14.)

Frans, 09:14: "What else can we do to find bugs? We do have plenty of
usage today." To the coordinator's six proposals, 09:21: "Start 1 to 4.
Don't do 5. Tell me more about 6." (1, a kill-and-restart harness; 2,
fuzzing; 3, long runs of the randomized harnesses; 4, two reviews, of
the indexes' concurrency and of the Javadoc against behaviour; 5,
opening 2026.3's and 2026.2's databases, not done; 6, SpotBugs.)


## 2. Ground rules

* Effort: the session xhigh; subagents xhigh until 22:00 (Frans, 09:22:
  "Use effort xhigh"; 09:23: "For today until 22:00, use effort level
  xhigh for subagents unless I say otherwise"). Usage plenty: 19 % of
  the week at 08:54, the week resets today at 22:00.
* Agents: up to 10 at a time until 22:00 (Frans, 09:41); before, 8
  (Frans, 2026-11-08, 22:12).
* F53: 006-16's CORE timings need it quiet in gaps until 13:00; heavy
  runs wait or go to s1.
* Nothing new into 2026.4 after the release candidate.
* The machine's quiet work after 22:00 (Frans, 11:40: "Let's move
  "night.sh large" and other work that needs a silent machine until
  after 22:00. We have so much usage left before the reset at 22:00. So
  let's reserve the time before 22:00 to coding and other AI use."):
  the release candidate's `night.sh large`, 022's quiet checks and
  006-16's CORE run in the night; until then, coding and reviews.


## 3. The work

* 020-13, the test study and bug hunt (coord-1108's agent t51, report
  by about 11:45); its fixes into `main` through coord-1109.
* 006-16, Props across releases (coord-1108's agent p48).
* 020-14, the Codex review (GPT-6.1-Sol, effort max), from 09:14.
* The bug hunts 020-15 to 020-19, from 09:23, each agent in its own clone
  and independent of the others until its report, by 15:00: a
  kill-and-restart harness (020-15), fuzzing (020-16), long runs of the
  randomized harnesses on s1 until 18:00 (020-17), a concurrency review
  of the indexes (020-18), the Javadoc against behaviour (020-19).
  Fixes come with a failing test, gated in the clone; the coordinator
  brings them into `main`, gated again, before the release candidate.
* The release candidate of 2026.4 after 020-13: `night.sh large` (about
  5 h), the jar tests on s1, jcstress, StreamDigest and the axioms; the
  tag at Frans's word.


## 4. If the coordinator stops

The state is in `/Users/f/fl/bench/coord/2026-11-09/state.md`. A new
coordinator reads it, this plan's progress, and the State notes of
020-13 and 020-14.


## 5. Progress

* 08:54 coord-1109 started; coord-1108 closing (t51 and p48 run in its
  process and report through it).
* 09:14 020-14: Codex started on a clone at `a9e5488`
  (`/Users/f/fl/bench/2026-11-09/codex/`).
* 09:23 020-15 to 020-19 started (agents k15, f16, s17, c18, j19, xhigh).


## 6. Outcome

Not yet.
