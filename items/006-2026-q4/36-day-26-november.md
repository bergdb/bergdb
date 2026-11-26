# 006-36 Day work, 26 November 2026

Created 2026-11-26 by Frans Lundberg. Status: active. The plan for the
lead's day of 2026-11-26 (lead-1126), a Thursday, and its night to
Friday 07:00: the progress and the outcome. The way of working is
013-04's (the lead).


## 1. The request

* Open from 006-35: 031-03's F1 to F6 (the design of `maintain()`),
  028-60's part 2, 028-62 and 028-54, all for Frans.
* `week.sh` takes about 15 hours since 028-63's envelope: bring it back
  to about 10 hours, at most 12 (028-64).


## 2. Decisions

Frans, 2026-11-26:

* 031-03, F6: 9.1 (RB-006's remaining part) and 9.2 (RB-010) confirmed
  as released bugs, S4; 9.3 a space cost, registered as 028-65 (09:46).
* `week.sh`: an aim of 10 hours, at most 12 (06:35); no whole-run hang
  guard (07:58); 028-64 landed and a full `week.sh` started (07:58).

* 031-03: no choice of F1 to F5 yet. A study first of `maintain(int
  budget)`, a call with a cost budget and passes that end by
  construction (031-04); a study of the direction, not a decision to
  build it (09:17).

The lead, 2026-11-26:

* 028-64 by one agent (Opus, xhigh) in a clone: coverage kept where the
  time can be won by running steps side by side, cut only where it
  cannot (class 1, how a task is done).


## 3. Progress

* 06:31 lead-1126 started; 06:32 lead-1125 closed (006-35 closed,
  `5f946d61`). Nothing ran.
* 06:35 Frans: `week.sh` to about 10 hours, at most 12. Its last run:
  579 minutes without the large reclaim run, which takes 5.5 hours on a
  typical seed since 028-63 (60 to 90 minutes on 028-43's local seed).
  028-64 registered; an agent started.
* 07:46 028-64 done (agent, Opus xhigh, 69 minutes): the large reclaim
  run and the large conformance set beside the other steps, each in a
  clone of its own; the same steps, seeds and sizes; about 6 hours
  estimated (5.5 to 6.7). 08:01 the whole-run hang guard removed (Frans);
  `week.sh short` WEEK OK (13 minutes). Landed, with `AGENTS.md`'s and
  013-04's times of `week.sh`; a full `week.sh` started on `main`.
* 06:47 to 08:10 031-03 gone through with Frans: the witness and the
  drain; MIN_RELEASE and the step reserve; `maintain()` as the
  application's idle-time hook with a budget per call; the stream kept,
  the live bytes and the space amplification, kept / live.
* 09:20 031-04 registered (the study); one agent (Opus, xhigh) in a
  clone, stop 13:30; Codex's review after it.


## 4. Waiting for Frans

* 031-03, F1 to F5: wait for 031-04's study.
* 028-60, part 2: B1, B2 or B3 (B2 recommended).
* 028-62, RB-011: J or S (S recommended, if its design stays small).
* 028-54: whether P2 covers a restart inside a commit's maintenance.


## 5. Outcome

(At the end of the day.)
