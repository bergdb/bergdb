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
* 15:58 P4's plans done: 016-06 (eight reviews tonight, R1 to R8; S1
  and S2 after the release), 016-07, 016-08 (H4 run by the coordinator;
  `night.sh large` does not fit).
* 15:59 Review R1 (handles and the node table) started, base `6f932f0`.
* 16:01 s1, JDK 27: `BEFORE COMMIT OK (121 s)`, the first run of the
  unit tests and f-tests on Linux on record; `level1.sh`, the night tests
  and the same on JDK 17 follow (016-08, L1 and L2).
* 16:02 jcstress on F53 started (016-08, F1). Homebrew's install of
  `openjdk@17` had upgraded seven shared libraries (brotli, freetype and
  others); `openjdk` 27 itself is unchanged.
* 16:03 P1's plans done: 016-03, 016-04, 016-09, 016-10. Chosen from
  their recommendations: ScaleBench at 200 MB only (no 10 MB runs), the
  quick `ab` with two runs per scenario, Props three runs each, no
  Shenandoah; the source zip without `releases/2026.1/`; the write-ups
  of 005-65 and 005-52 after the quiet block.
* 16:04 Committed `323a54a`: the plans 016-03 to 016-10. All detailed
  plans are in place.
* 16:04 The tools agent T started (016-10's scripts, then 016-09's). The
  005-65 rerun's smoke test started.
* 16:05 jcstress on F53, today's five tests on `6f932f0`: all OK, and
  the control saw its race (016-08, `08-tests/results.md`). JDK 17's
  `before-commit.sh` and night tests on F53 started (016-08, F2). 005-65's
  rerun smoke-tested and READY for window 2.
* 16:09 JDK 17 on F53: `BEFORE COMMIT OK (76 s)` and the night tests'
  SUCCESS (016-08, F2). 16:10 the stress runner's smoke OK; F3, the
  stress programs with fresh seeds, two hours from 16:10.
* 16:08 s1, JDK 27: `level1.sh` and the night tests failed on the
  machine, not on BergDB: the OOM killer took one of `level1.sh`'s four
  parallel `-Xmx2g` RestartStress JVMs (3 GB of memory), and
  `BryanIssueNight` filled `/tmp`, a 1.9 GB tmpfs ("No space left on
  device"). Rerun queued with the temp files on the disk and the four
  JVMs one after another, in s1's copy only (016-08, section 2, "A
  failure").
* 16:11 Hand-offs waiting for review (H5), with no free slot: 005-79's
  Part A (`679e153` in its clone; `BEFORE COMMIT OK`, LEVEL 3 OK, the
  decided digests identical, 36 of 36) and 005-82 (`BEFORE COMMIT OK`;
  three tests, each fails on the base).
* 16:12 Registered from the agents' findings: 015-07 (Fix, for 2026.2: the
  node parsers do not check their inner fields, and such a read does not
  fail the database; verified by a probe; F1 takes it next) and 015-08
  (Fix: StreamDigest's compare reports the physical cut, which depends on
  timing).
* 16:16 to 16:18 Reviews (H5) by the coordinator, to keep the commits
  moving while the four slots are busy: 005-69, 005-71 and 005-82, no
  faults (one nit in 005-82, taken); 005-79's Part A, no faults (its
  integer forms checked: `fractionOf`'s split, `lowOf`, the buffer
  sizes; a non-default internal fraction is now the nearest multiple of
  2^-16, for the notes). 015-09 registered (Fix: a reclaim test of
  `before-commit.sh` that fails under load).
* 16:18 The combined gate of 005-79 A, 005-69 and 005-71 queued behind the
  agents' gates (one at a time).
* 16:21 Combined gate of 005-79 A, 005-69, 005-71 and 005-80:
  `BEFORE COMMIT OK (97 s)`. Committed: `dde82e8` (005-79 Part A),
  `b281d39` (005-69), `af6e762` (005-71), `522b645` (005-80). 005-69,
  005-71 and 005-80 are done.
* 16:24 005-82 gated on `main` (`BEFORE COMMIT OK (110 s)`) and committed,
  `3e32f02`; done.
* 16:30 005-79's Part B handed off (`BEFORE COMMIT OK (140 s)`; the
  decided digests change in 1 of 12 configurations, by one take of 2,158).
  Its review (H5) by an agent started at 16:42.
* 16:39 Review R1 (handles and the node table) done, in 41 minutes: four
  faults and two doubts (`06-reviews/R1.md`). Registered: 015-12 (Fix: a
  key node's growth publishes its arrays before their contents; a search
  can miss a key or read a later transaction's value; seen by probes on
  F53, rare; also in 2026.1), 015-15 (Fix: the resident count drifts
  below the real bytes), 015-13 and 015-14 (Decide, for Frans: the
  handles' bytes not counted; the fast path's argument rests on the
  address dependency). The coordinator chose 015-12's fix: a release
  fence on the writer's side, no cost to readers.
* 16:43 s1: the night tests pass on JDK 27 and 17 with `/tmp` on the
  disk, the first on Linux on record. 015-10 (CapacityTester failed twice
  in the tools agent's runs on s1 under load) not reproduced in six runs;
  open. 015-11 registered (the tests' temp files ignore
  `java.io.tmpdir`). 16:44 s1: jcstress, then the disk stress programs
  until 23:30 (016-08, L3 and L4).
* 16:47 005-52's PauseProbe change gated on `main` (`BEFORE COMMIT OK (89
  s)`) and committed, `87d1e2c`. 005-79's agent done: Part B is
  `ddbba95` in its clone, `BEFORE COMMIT OK (139 s)`, LEVEL 2 OK
  (RestartInvariance identical in 8 configurations, TRACECHECK OK); its
  review runs.
* 16:48 Agent K started: 015-12, then 015-15 (R1's faults).
* 16:52 015-07 gated on `main` (`BEFORE COMMIT OK (113 s)`) and
  committed, `12610c7`; done. 005-52's night script smoke-tested
  ("lowered (SMOKE): OK") and READY; both steps of the quiet block are in
  `steps.txt` (65-rerun, 52-lowered).
* 16:52 F3 (the stress programs, fresh seeds) has two failed chunks of
  about a thousand: `PowerLossTest` once in its cleanup ("cannot delete
  test file"; three reruns of its seed OK) and `InterruptStress` once (a
  get during a close failed with "File closed", and the close reported
  it). Registered as 015-16 and 015-17 (Investigate), for an agent.
* 16:56 The tools agent's W7 steps smoke-tested; their five lines added to
  `steps.txt` after 005-65's and 005-52's (READY at about 01:55, by
  `prep-a.sh` on the release's jar).
* 16:58 Review of 005-79's Part B: no fault in the code (the fixed-point
  take against BigInteger, divlu, the overflow bounds, T3, the digests);
  a test gap (one comparison that decides l3-node14's bytes is not pinned
  by a test), two wrong Javadoc dates and a half-true sentence in
  `lean/README.md`. The author answers them, then the commit.
* 17:06 015-12 (R1-F1) gated on `main` (`BEFORE COMMIT OK (102 s)`) and
  committed, `dc42409`; done. Its jcstress test fails on the code before
  and passes with the fence; R1's probes go to zero.
* 17:04 Frans checked in; told that nothing blocks, and the three
  optional decisions (015-13, 015-14, 005-78) with their recommendations.
* 17:10 Usage tight (the 5-hour window at 81%, 54% of it gone; extra
  usage on). New agents at high effort until the reset at 19:30, still
  up to four (Frans's word); Frans asked once.
* 17:15 005-79's Part B gated on `main` (`BEFORE COMMIT OK (153 s)`) and
  committed, `f04cefe`; 005-79 done for 2026.2 (Java), Lean and C after
  the release (015-03, 015-02). s1: jcstress's five tests OK on Linux.
* 17:19 015-01 with 015-06's first part gated on `main` (`BEFORE COMMIT
  OK (142 s)`) and committed, `ed16384`: 015-01 done; 015-06 in progress
  (a start refused after the open still leaves the first file).
* 17:25 Frans: "Avoid consuming extra usage. Restart agents at high
  effort if needed. Hold new starts until 19:30 if needed." The 5-hour
  window at 92%; the four agents stopped at safe points with their State
  notes (015-09's fix ready, not gated; 015-10's stop rule proposed;
  015-13 half done in K's clone; 015-16 found: the tester's `stop()`).
  No new start until 19:33.
* 17:27 015-15 (R1-F4) gated on `main` (`BEFORE COMMIT OK (137 s)`) and
  committed, `f82e7e7`; done.
* 17:31 015-17 (F3's `InterruptStress`) gated on `main` with the patch
  (`BEFORE COMMIT OK (130 s)`) and committed, `6105d21`; done: close()
  reported a get's "File closed". 015-19 registered: tools in items that
  still use what 005-79 removed (after the release).
* 17:57 Frans: xhigh for every agent, no split by task; the pace is set
  by the number of agents at a time.
* 18:04 Frans: reviews on Codex (GPT-6.1 Sol, effort max), from Codex's
  own quota. R2 and R3 started 18:05 (016-06, section 9).
* 18:11 F3 (the stress programs, 2 hours): 3,407 runs, two failed, both
  known: 015-17 (fixed) and 015-16 (016-08's results).
* 18:45 R2 done: 5 faults, 1 doubt. 19:13 R3 done: 12 faults, 4 doubts,
  13 tests to add. Of the 17 faults, two are new in 2026.2 (R2-F1,
  R3-F3); the others are in 2026.1 too.
* 19:20 Codex's usage limit: R4, R5 and R6 (started 19:15) stopped; they
  continue at 23:09.
* 19:33 Claude's 5-hour window reset; usage plenty. Started: verify-1
  (eight of the 17 faults: the two new ones and those that can give a
  wrong answer or lose data), 015-14 and 015-10, at xhigh. 015-13 waits
  for 015-10 (both change `Eviction`). 015-09 and 015-16 reviewed by the
  coordinator, in the combined gate.
* 19:39 015-09 and 015-16 committed (`d91b619`, `cf6c8e7`), done; gate
  `BEFORE COMMIT OK (103 s)`.
* 19:44 verify-1: all eight confirmed; 015-20 to 015-27 registered
  (`c657764`). 19:50 the index faults (015-20, 22, 21) and 015-24 started.
* 19:57 Usage at 14% with 9% of the window gone, and extra usage on: three
  agents at a time from now; 015-26 and 015-23 put off.
* 19:59 015-10 committed (`24bdae5`), done: the eviction thread's stop
  rule; gate `BEFORE COMMIT OK (115 s)`.
* 20:06 015-24 committed, done: the directory lock across class loaders,
  new in 2026.2; gate `BEFORE COMMIT OK (107 s)`. The docs agent started
  (016-03, 016-04).
* 20:10 015-14 handed off; its review (20:30): no fault. The new jcstress
  tests show that F53 reordered the two loads of the fast path on the
  code before (a harmless outcome, as `usable` checks it); R1-F3's wrong
  answer was not seen. The fix makes the order hold by the memory model.
  Its doc nits are being fixed; the read path's cost is unmeasured.
* 20:10 to 20:30 the docs agent: next.md complete (`e5bd275`), the draft
  notes (outside the repository until R9), replication's Javadoc
  (`777f75f`), README.md and docs/levels.md (`fe72238`, `b6515aa`, with
  015-27's correction of section 3), 2026.1's post-release notes
  (`44bfaae`); D4 and D6 no change. N4 at about 01:00.
* 20:31 015-20, 015-22 and 015-21 committed (`9971100`, `7cd4cdb`,
  `377fe7d`), done; review: no fault; gate `BEFORE COMMIT OK (104 s)`.
  The review met two more faults of 2026.1, registered as 015-28 and
  015-29, and 015-30 (time only).
* 20:29 Usage at 35% with 20% of the window gone: at most two agents until
  00:30.
* 20:36 015-14 committed (`4e10aa2`), done. 20:48 015-13 committed
  (`e427a4c`), done: the handles are counted; at a given cache size about a
  third fewer objects stay in memory. 20:56 015-25 committed (`fa08db4`),
  done: an eviction batch that throws fails the database.
* 20:56 verify-2: R2's and R3's other nine findings confirmed, all in
  2026.1 too: 015-31 to 015-39.
* 21:25 S1 (rw-transactions, encryption, JMX): 9 faults with failing tests,
  all in 2026.1 too: 015-40 to 015-48. 015-40 (a put and a delete of one
  key in one transaction keeps the put) is being fixed. 21:26 S2 (indexes
  and objects): 27 faults with probes, all in 2026.1 too: 015-49. Item 9 of
  section 7.

* 22:20 to 07:24 the session stopped: its OAuth token refresh was refused
  (HTTP 400; "OAuth refresh token is no longer valid"), and every later
  request failed; docs/log.md, 2026-11-04. Not done: the release steps of
  00:45 to 02:50, Codex's reviews after 23:06, the morning. Done without
  the session: `night.sh` 02:10, NIGHT OK on `3386ade` in 38 minutes (all
  the night's fixes; the gate on the release's code, as commit A adds
  BuildInfo only); the quiet block's 65-rerun and 52-lowered, exit 0; s1's
  L4 stress on `3e32f02` failed once in `interrupt`, 015-17's fault (fixed
  in `6105d21`). R8 wrote its report before it stopped: 10 faults,
  015-56 to 015-64 (R8-F1 is 015-36); 015-56 (R8-F10) is new in 2026.2.
* 07:39 Frans: unattended until 12:00; the W7 numbers in tonight's quiet
  block; section 7's items 6 to 9 as recommended. The plan to 12:00:
  015-56's fix (agent, review, gate, commit); the rehearsal; commit A
  (`set-buildinfo.sh 2026.2 262`, before-commit); `build-a.sh`;
  `tests-f53.sh` and `s1-chain.sh`; N4 (the notes agent); `collect.sh`,
  `axioms.sh`, `finish.sh`; R9 (`stage-b.sh`, commit B, the tag
  `release-2026.2` on A, local); news.md by 12:00. Codex reviews R4, R5
  and R6 again on `f5a5f66` (stop 10:30); their faults go into the notes as
  known issues. Tonight: the W7 numbers on A's jar (016-10), a conductor
  of night 2.


## 7. For Frans to decide

Frans's answers, 2026-11-03, 17:18, to items 1 to 5 below: "1. As
recommended. 2. Tell me more. 3. It can be run later. Let's just ensure we
remember to. 4. This seems straigh-forward. If it really is
straight-forward and you have a proposal, fix it before the release. 5.
"thread safety rests on today's JVM behaviour". This is not acceptable.
Ensure this is either fixed before the release or clearly documented as an
open todo item. This needs an investigation and a fix."

* 1: 015-05 after the release, B1 recommended; a known issue of 2026.2.
* 2: explained to Frans at 17:20 (S1 and S2 cover the parts the C clone
  did not port; about 90 lines changed since 2026.1; R1 took 41 minutes).
  Frans, 17:21: "Yes, as recommended." So S1 and S2 run tonight after
  R2 to R8 and 015-14, if they can start by about 22:00; a fault they find
  is fixed by 01:00 or a known issue.
* 3: `night.sh large` after the release, registered as 015-18 so that it
  is not forgotten.
* 4: 015-13 is fixed before the release (R1-F2's proposal: the handles
  counted as 009-02, 4.7 says), by agent K after 015-15.
* 5: 015-14 becomes a Fix: an investigation and a fix (acquire reads, or
  what the investigation finds) before the release, by its own agent;
  if not done by the freeze, an open Fix entry and a known issue of the
  notes, said plainly.

1. **015-05: a start on an empty or missing directory** (015-01's case
   3), for after the release. Recommended: B1, `createIfMissing()`, in the
   first release with a public API; until then the recipe in
   `DatabaseBuilder.start()`'s Javadoc.
2. **The reviews left out tonight** (016-06, section 7): S1
   (rw-transactions, encryption, JMX) and S2 (indexes, objects). The run
   goes on with A, after the release; B would run them tonight, C would
   release a day later.
3. **`night.sh large`** (016-08, section 6): it does not fit before the
   release commit. The run goes on with A: tonight the large conformance
   set without its two `l-big62` traces, and the whole of `night.sh large`
   on the release commit after the quiet block.
4. **015-13: the resident bytes count no handle** (review R1, R1-F2): a
   database uses 34 to 49 percent more memory than its budget in R1's
   probe. Recommended: count them as 009-02, 4.7 says, after the release;
   a known issue of 2026.2.
5. **015-14: the fast path's plain reads rest on the address dependency**
   (R1-F3), not on the JMM as 009-02, 3.4 says. Recommended: state it in
   009-02 for 2026.2, then measure acquire reads (T6a) and take them if
   they cost little.

Open since 19:45; Frans, 2026-11-04, 07:39, items 6 to 9: "Yes, as
recommended":

6. **015-27: a failed append's transaction was already visible** (review
   R3, R3-F8, confirmed by verify-1): a get beside a put whose append
   fails can see the put's values; `docs/levels.md`, section 3, says a
   transaction is visible only once stored. Recommended: correct the text
   for 2026.2 (what a reader may see before a failure), and decide on the
   code after the release; a change of the code is a change of the
   writer's protocol.
7. **Which review faults block the release.** Of the 17 faults of R2 and
   R3, 8 are confirmed so far, 2 of them new in 2026.2 (015-24, 015-25).
   As 016-06, section 6: the new ones and those with a wrong answer or
   lost data in normal use (015-20, 015-21, 015-22) are being fixed now;
   what is not fixed by 01:00 is a known issue of 2026.2, and the release
   does not wait for it. Recommended: as that.
8. **015-24's mechanism** (committed tonight): to refuse a directory that
   a copy of BergDB in another class loader holds, each copy records its
   locked directories as system properties (`bergdb.lock.KEY`), a JVM-wide
   registry. The alternatives were the platform MBean server (needs
   `java.management`) and a second lock file (a new file in the database
   directory). Recommended: keep it; a copy of 2026.1 in the same JVM still
   has the old fault.
9. **The Pub API's upper layers have many old faults.** Tonight's reviews
   of the indexes, the objects and the rw-transactions (R3, S1, S2) found
   about 45 faults that 2026.1 has too: 3 of them fixed tonight (015-20 to
   015-22), 015-40 in progress, the rest registered (015-23, 015-28 to
   015-30, 015-36, 015-37, 015-39, 015-41 to 015-49; S2's 27 in 015-49). Some give wrong answers in normal use (S2: `prefix()`,
   `inclusive(false)` without `startAt()`, later composite levels; S1: a
   put and a delete of one key in one transaction). Recommended: release
   2026.2 with them as known issues, the notes saying plainly that the
   index and object layers have known faults, in 2026.1 too; after the
   release, an item of its own to verify and fix them. Alternatives: mark
   indexes and objects experimental, as replication; or hold the release
   for fixes (days, not hours).


## 8. Outcome

Not yet.
