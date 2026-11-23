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


## 5. Outcome

Not yet.
