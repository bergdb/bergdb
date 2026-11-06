# 006-13 Day and night work, 6 to 7 November 2026

Created 2026-11-06 by Frans Lundberg. Status: open. The plan for the
coordinator's day and night of 2026-11-06 (coord-1106), the progress and
the outcome. The way of working is 013-02's (the coordinator) and, for the
night, 013-01's.


## 1. The request

Frans, 2026-11-06, 08:14: "You are coord-1106. Coordinator for today's and
tonight's work."

Frans, 09:18: "Walk me through the items of For Frans to decide. Start
with 1." (006-12, section 8, "For Frans to decide", ten points.)


## 2. Ground rules

* Effort: xhigh for the session and every agent; high when the usage level
  is `tight` or `limit` (013-02).
* Agents at a time: at most 4 (as yesterday, until Frans says otherwise).
* Commits to `main` by the coordinator, by path, in Frans's name, with no
  AI attribution; Java changes after `BEFORE COMMIT OK`.


## 3. The work

### W1. 006-12's decisions

The ten points of 006-12, section 8, one at a time with Frans.

1. 019-10, R5's F1 and F2 (an `Error` of a read). Discussed 09:18 to
   09:38. A read changes no state of BergDB's streams (`BufferedStream`,
   `FileStream`, `SalsaStream`), so a third option came up: (c) an
   `Error` of a read is thrown as it is and the database goes on. Frans,
   09:38: "If we can really ensure the database as a whole is still in a
   good state after an OOM in a get, we should allow the database to go
   on. At least if this does not become too complex to implement and
   understand. KISS is an important principle. Important that the database
   user understands the error model. That is part of the interface."
   Agent e1 (read-only) checks whether that can be ensured, and drafts the
   error model; section "Can the database go on after an Error in a
   read?" of 019-10.
2. 015-80's C1 (Reclaim's cut waits for the thread's append, holding
   the write lock). Frans, 09:47: "As recommended." Done: a line under P1
   in 010-01 (a deviation), and 019-36 to measure the wait on F53 and s1
   and, if it is over the target, R4's `tryLock` fix.

### W2. KISS as a principle

Frans, 09:47: "Also, add KISS to our principles 010. Keep it short and
simple. Always important. Also with AI, even though more complexity can be
sustained now." Done: 010-P13, "KISS".


## 4. The principles

010's: P1 (no stop-the-world in BergDB's own code, about 20 ms), P7 (a
database whose environment has failed, or that has a bug, does not run
on), and P13, KISS (Frans, 09:38 and 09:47).


## 5. Timeline

None yet.


## 6. If the coordinator stops

The state is in `/Users/f/fl/bench/coord/2026-11-06/state.md`; a new
session continues with `/coordinator resume` (013-02).


## 7. Progress

* 08:14 coord-1106 started; main 8df56fc.
* 09:18 W1 started: 006-12's decisions with Frans.
* 09:40 Agent e1 started (019-10, read-only, xhigh).
* 09:47 Point 2 decided; 019-36 registered; 010-P13 KISS added.


## 8. Outcome

Not yet.
