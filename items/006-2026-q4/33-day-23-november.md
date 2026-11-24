# 006-33 Day work, 23 November 2026

Created 2026-11-23 by Frans Lundberg. Status: open. The plan for the
lead's day of 2026-11-23 (lead-1123), a Monday, and its night to
Tuesday 07:00: the progress and the outcome. The way of working is
013-04's (the lead).


## 1. The request

Two pieces of work, the release first:

* The release 2026.6, planned for Tuesday 24 November: the steps of
  026-27, section 2, that fall on Monday, steps 1 to 11.
* The 013-04 implementation, plan steps 2 to 6
  (`items/013-ai-work/04-lead/plan.md`, section 12), in a clone, by two
  agents; it lands after Frans has looked at it.

Decisions (Frans, 2026-11-23):

* 026-27's D1 to D5 as recommended there: of the release runs only
  night.sh is repeated, on `main`'s head; the timing figures do not
  block and the notes name them; Codex reviews 030-38; the extra checks
  of D4 (jcstress, the jar's tests on JDK 27 and 17 on s1) run on commit
  A in the night, and a failure stops the release for a look; the tag's
  message is `BergDB 2026.6, 2026-11-24`.
* The lead commits and pushes to `main` the work in items and documents
  (030-38, the review's findings, 030-26, 033, `releases/next.md`) and
  the adapted release scripts, each after its gate. Commit A stays in a
  clone; it goes into `main` on Tuesday with Frans (026-27, step 12).
* A change to a pinned Lean statement or a checker lands with GATE OK
  and LEVEL 2 OK. A change that weakens a proved guarantee waits for
  Frans.
* A failed gate or D4 check stops that path of the release; the other
  work goes on, and the failure is in the morning summary.
* No quiet block: no timing run in the night.
* Both pieces run in the night: the release first, 013-04's agent A in
  parallel, agent B after A. The night's agents stop at 30 % of the new
  week (it resets at 22:00); B is the first to give way when the release
  needs more.


## 2. The ground rules

* Subagents on Opus 5.5, effort high; xhigh for 013-04's agent B.
  Codex on its own quota.
* At most three agents at a time.
* The week's usage: the night stops starting agents at 30 %.
* Commits in Frans's name, no AI attribution; committed text is public.


## 3. The timeline

* 15:12 night.sh on `main`'s head (026-27, step 1), by the lead.
* 22:05, after the usage reset: 030-38, the guarantee list (026-27,
  step 2), by an agent; 013-04's agent A.
* When 030-38 is done: the Codex review (step 3), then the findings
  closed (step 5), and steps 6 to 9.
* In parallel: the release scripts (step 10).
* Then commit A in a clone and its gate (step 11), and the D4 checks.
* When A's tests pass: 013-04's agent B.
* By 07:00: the morning summary in `news.md` and section 5.


## 4. Progress

* 15:12 night.sh started on 8056d259.
* 18:13 NIGHT OK (181 minutes), every step ok; java/build/night/2026-11-23-1512/report.txt. 026-27, step 1, done.
* 22:14 After the week's reset: three agents (Opus, high): 030-38 (026-27, step 2), the release scripts (step 10), and 013-04's agent A (its plan's steps 2 to 4).
* 22:20 030-38 written (14 guarantees: 9 proved, 5 tested; 8 differences from 030-26), 951e15f9. 22:23 Codex review of 030-38 started (026-27, step 3).
* 22:22 Release scripts adapted and smoke-tested on scratch repositories (026-27, step 10, section 4). release.sh needs README.md's text for after the release (READMEMD), written by hand.
* 22:28 Codex's review of 030-38: nine findings, three of them overclaims (C-STEP does not fix the reclaim row's key; power-loss durability needs forcing on; reads beside reclaim may expire). 22:36 an agent (Opus, xhigh) closes them and brings 030-26 up to date (026-27, steps 5 and 7).
* 22:29 013-04, agent A: usage.sh, status.sh and watchdog.sh with their tests (LEAD TESTS OK, 106 checks), in the implementation clone. 22:32 agent B (Opus, xhigh): SKILL.md, the state template, 013-04's description, Codex's review.
* 22:34 026-27 steps 6, 8 and 9 done: 030's goal 2 recorded as done; 033 checked (RB-001 to RB-003, no new entry); releases/next.md complete. README.md's text for after the release drafted for Frans, outside the repository.
* 23:09 026-27 steps 3, 5 and 7 done: the review recorded as 030-39, its nine findings and 030-38's eight differences closed; C-STEP checks the reclaim row's key (GATE OK, 254 theorems; LEVEL 2 OK; LEVEL 3 OK); 030-26 current. 23:13 step 11 started: commit A in a clone, its gate and the D4 checks.
* 23:37 013-04, agent B: SKILL.md (120 lines), the state template and 013-04's description rewritten (its plan's steps 5 and 6); a fresh agent answered all twenty sample decisions; Codex's review in seven rounds, 17 of 18 points fixed, one for Frans. In the implementation clone, for Frans's review.
* 00:12 026-27 step 11 done: commit A, bbcd802f (BuildInfo 2026.6; releases/next.md in line with 030-38 and 030-39), in a clone, not pushed. Its gate in a new clone: BEFORE COMMIT OK; lake build OK; GATE OK (254 theorems, 144 pinned files); MODEL AXIOMS OK; StreamDigest: all 12 configurations differ from 2026.5, each named in the notes. D4: JCSTRESS OK (8 tests); the jar's tests on s1, JDK 27 and 17: S1 TESTS OK. Steps 12 to 16 wait for Frans.


## 5. Outcome

Written 2026-11-24, 06:15, by the lead (lead-1123). The week's usage at
06:11: 3 % (the night's limit was 30 %).

Done, in `main`:

* Release 2026.6, 026-27 steps 1 to 10, and step 11 in a clone: NIGHT OK
  on 8056d259 (step 1); 030-38, the guarantees G1 to G14, nine proved and
  five tested (951e15f9); the release scripts adapted and smoke-tested
  (4583ca02); 030's goal 2 done, 033 checked (RB-001 to RB-003, no new
  entry), `releases/next.md` complete (e28aeb7d to 7e0a9c10); Codex's
  review of 030-38 as 030-39, its nine findings and 030-38's eight
  differences closed, C-STEP checks the reclaim row's key (GATE OK, 254
  theorems; LEVEL 2 OK; LEVEL 3 OK), 030-26 current (a6ae4263 to
  d8ac615c); 026-27's log (8f719650).
* Commit A, `bbcd802f` on `d8ac615c`, in a clone, not on `main`: BuildInfo
  2026.6 and next.md in line with 030-38 and 030-39. Its gate: BEFORE
  COMMIT OK, `lake build` OK, GATE OK, MODEL AXIOMS OK, every StreamDigest
  configuration that differs from 2026.5 named in the notes (all 12).
  D4: jcstress OK (8 tests); the jar's tests on s1, JDK 27 and 17, OK.

The night: nothing failed. 013-04's agents A and B finished steps 2 to 6
of its plan in the implementation clone (head 05f8b922; LEAD TESTS OK,
rerun by the lead): usage.sh, status.sh, watchdog.sh and their tests;
SKILL.md (120 lines), the state template and 013-04's description; a
fresh agent answered twenty sample decisions; Codex's review in seven
rounds, 17 of 18 points fixed. Not in `main`: it waits for Frans's
review.

For Frans to decide:

1. **The release, steps 12 to 16.** Read the notes (`releases/next.md`
   in A) and README.md's text for after the release (a draft by the
   lead, given to `release.sh` as READMEMD). Recommended: go on with
   `to-main.sh` for A (`main` moved in `items/` only since A's parent, so
   it merges), then `release.sh`, the tag and the GitHub release.
2. **Two gaps accepted for 2026.6** (030-39, F4 and F7; stated in 030-38
   and the notes): the reclaim theorem's run restarts at every cut; the
   admission count for value transformations is argued, not proved.
   Recommended: accept for 2026.6.
3. **Three proposed 028 entries** (030-39, section "Actions"): the
   contract checker fails a trace with a shape fault; a test of
   `Db.checkDirtyNodes`' count for key and value transformations and the
   cheap estimate; DagTester's multilevel deletes at node size 62 with
   join heights asserted. Recommended: register all three after the
   release; none blocks it.
4. **028-07's date race** (033's log): it could have written a wrong date
   in `created.txt` at midnight in 2026.5; never seen. Recommended: no RB
   entry; 033's log records it.
5. **013-04's new skill** (the implementation clone, 05f8b922; the item's
   section 12). Recommended: review it today, land it (its plan's step
   8), and start lead-1124 on it, its night the test (plan 9.2).
6. **013-04's SUMMARY DUE** only for a lead that ran before 06:00 that
   day (the plan's section 4 says from 06:00 for any lead). Recommended:
   keep it so.

Left: 026-27 steps 12 to 16 (Tuesday, with Frans); 013-04 plan steps 7
to 9.
