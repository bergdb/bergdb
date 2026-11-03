016-02. The run
===============

Created 2026-11-03 by Frans Lundberg.

**Status: in progress.** The record of the work on release 2026.2 (016-01,
section 8, "The log"): the request, the subitems and agents, the timeline,
the progress with times, the stops for Frans and the outcome. It takes the
place of a 006 subitem for the days of the release. The coordinator's
minute-by-minute state is in `/Users/f/fl/bench/coord/2026-11-03/state.md`.


## 1. The request

Frans, 2026-11-03, 15:27, to the coordinator (013-02):

> You are the Coordinator for the unattended work to create BergDB
> release 2026.2. See item 016 for scope and the plan. Work unattended
> unless I interact with you. Start subagents for actually coding and
> other task so you as the coordinator session stay responsive. Your are
> allowed to start up to 4 subagents running at a time.
>
> Another session is creating the 016-01 overview plan. When it is done,
> create detailed plans for all works items needed to create the release
> package. Each detailed plan receives a subitem of 016. You can also use
> todo items in 005 and 015. When more todo items are discovered during
> this work, add them as subitems to 015, the new collection of todo
> items. Solve such items when they belong to the scope of release 2026.2.
>
> When the detailed plans are in place, implement all the plans until
> completion. Run subagents in parallel when possible. Commit the work in
> my name, Frans Lundberg. Work with unattended until 07:00 in the
> morning. Report to me by that time by reports of progress in items and
> in news.md. The author of code and documents should be me, Frans
> Lundberg, not AI.
>
> Questions of 016-10 section 11.
>
> Q1: as recommended.
> Q2. Yes on both as recommended.
> Q3. Use xhigh, no higher.
> Q4. Fix before. You decide how to.

("016-10 section 11" is 016-01, section 11.) And at 15:31:

> A change. The C code does not need to be updated for 2026.2 in this
> work. Only Java code will be included in the release. It is not a
> rewqurement to update the Lean code either. If this is needed to
> develop Java or to ensure it works well, then do it. See it as a tool,
> not an output artifact for the release.

Both are recorded in 016-01, section 10 (the answers, and D7).


## 2. Ground rules

016-01, section 3, and 013-01, section 4, with these:

* **At most 4 subagents at a time**, each at xhigh effort (Q3; high only
  when the usage level is tight, 013-02).
* **Java is the release** (D7). The C clone is not updated. Lean is
  changed only where it helps to develop or check a Java change.
* **Authorship.** Code, documents and commits are Frans Lundberg's: the
  commits in his name with no AI attribution, the documents' headers
  "Created ... by Frans Lundberg", no AI named as an author.
* **New todo items** found on the way are registered by the coordinator
  as 015 subitems, and solved before the release when they are in its
  scope (016-01, section 6, the rule for findings).
* **Nothing is pushed**, and the tag stays local (016-01, section 3).


## 3. The subitems

Numbers allocated by the coordinator at 15:30. The detailed plans:

| ID     | What                                                       | Plan written by |
|---|---|---|
| 016-03 | W1 and W2: the release notes, 2026.1's post-release notes | agent P1 |
| 016-04 | W3 and replication's wording: the documents                | agent P1 |
| 016-05 | W4 and H5: the fixes before the release, and their reviews | agent P3 |
| 016-06 | H1 and H2: the reviews of the changes and of the Pub API   | agent P4 |
| 016-07 | H3: concurrency                                            | agent P4 |
| 016-08 | H4: the tests beyond the gates, Linux and JDK 17           | agent P4 |
| 016-09 | W6: the release, by 008-01's steps                         | agent P1 |
| 016-10 | W7: the numbers against 2026.1                             | agent P1 |

The entries of W4 hold their own plans: 005-79 and 005-78 (agent P2);
005-82, 005-69, 005-71, 005-80, 005-52, 005-65 and the new 015-01, the
empty directory (agent P3).


## 4. The timeline

Frans, 15:40: "Regarding the plan of 016-01. I want you to try your best
to finish this work by 07:00 tomorrow in the morning. I know you are fast,
so give it your best to finish by then instead of in three days or so.
Note, you only need before-commit.sh to be successful to commit your
work."

So 016-01, section 8's four days become one night, and the only commit
gate is `java/before-commit.sh` (`BEFORE COMMIT OK`) on the combined tree.
The plan (times planned; the progress below has the real ones):

* 15:30 to 16:50: the four planning agents.
* 16:50 to 17:15: the coordinator checks the plans, chooses 015-01's
  design, and commits the plans.
* From 16:50: implementation and the search at once, four agents at a
  time: the fixes (016-05), the reviews H1 to H3 (016-06, 016-07), the
  documents (016-03, 016-04), the JDK 17 and Linux runs (016-08). Each
  change is reviewed by another agent (H5), copied into `main`, gated and
  committed.
* By about 01:30: every fix and verified finding committed; the night
  scripts READY; the release commit A (016-09) by 01:45, and its jar.
* 01:45 to 02:05: W6's tests on the jar on F53 where they fit.
* 02:00: s1's runs (W7, and the jar's tests there) from the conductor.
* 02:10: `night.sh` on A, the release's gate (about 45 minutes).
* From night.sh's end (about 03:00) to 06:05, the quiet block (window 2):
  005-65's `threads.sh`, 005-52's runs, then W7's F53 block. The session
  is idle; no check-ins from 03:00 to 05:59.
* 06:07 to 07:00: the numbers into the notes, commit B and the tag, this
  subitem's Outcome and the summary in `news.md`.

005-78 waits for Frans's choice of a form (a format question, 016-01,
section 3). Unless he chooses before the release, it is a known issue of
2026.2, and its design is in "For Frans to decide".


## 5. If the session stops

* The watchdog (013-02, section 8) runs until 2026-11-04 07:00 and
  writes `news.md` if the session's process is gone.
* The conductor runs the quiet block without the session, and writes a
  fallback summary at 06:50 if the session wrote none.
* Each agent keeps a State note in its item; the coordinator's state
  file lists the agents, so a check-in or a restarted session resumes
  them.


## 6. Progress

* 15:27 Frans's request; the coordinator goes unattended until 07:00.
* 15:29 Watchdog started; check-ins every 20 minutes (none 22:00 to
  23:59).
* 15:30 Four planning agents started: P1 (016-03, 016-04, 016-09,
  016-10), P2 (005-79, 005-78), P3 (016-05, the small fixes, 015-01), P4
  (016-06 to 016-08).
* 15:31 Frans: Java only (D7); the agents told.
* 15:32 Conductor started for window 1, 22:30 to 23:55.
* 15:33 Committed 6d81050: 016-01 with Frans's answers and D7, this
  subitem, 016's readme.
* 15:40 Frans: the release by 07:00; only `before-commit.sh` to commit.
  The agents told; the timeline above replaces the earlier one.
* 15:42 Conductor restarted: window 1 empty (s1 steps from 02:00),
  window 2 from night.sh's end to 06:05. Check-ins: none 03:00 to 05:59.
* 15:43 JDK 17 on s1: Temurin 17.0.21+9 in `/opt/bergdb-bench/jdk-17`
  (Q2). On F53, `brew install openjdk@17`: 17.0.21.0.3 in
  `/opt/homebrew/opt/openjdk@17` (not linked; the default java stays 27).
* 15:50 P2's plans done, in 005-79 and 005-78. Chosen: 005-79 as two
  commits, A (no byte change) and B (the take in fixed point), with A
  alone in the release if B is not gated by 00:30; no Lean step (D7);
  005-78 tonight only the study, the probe and the design for Frans.
* 15:51 005-79's implementation started (its plan is complete; the
  longest task goes first).
* 15:55 P3's plans done: 016-05, the plans in 005-82, 005-69, 005-71,
  005-80, 005-52 and 005-65, their night scripts, and 015-01.
* 15:57 Agent F1 started: 005-82, 005-69, 005-80, 005-71, in that order.
* 15:57 015-01 decided by the coordinator: A with A+ (`created.txt` as the
  mark of a database, the creation forced before it; a start refuses a
  directory with `created.txt` and no stream byte). Registered from the
  plans: 015-02 (C follows), 015-03 (Lean follows 005-79), 015-04
  (`deps.py`), 015-05 (an empty or missing directory, for Frans), 015-06
  (a refused start leaves an empty first file; fixed with 015-01).


## 7. For Frans to decide

1. **015-05: a start on an empty or missing directory** (015-01's case
   3), for after the release. Recommended: B1, `createIfMissing()`, in the
   first release with a public API; until then the recipe in
   `DatabaseBuilder.start()`'s Javadoc.


## 8. Outcome

Not yet.
