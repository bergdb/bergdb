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
3. 019-15 (key replace leaves a delete's key as written). Frans, 09:57:
   "This seems very hypothetical. I fail to understand why the user would
   want to delete delete("/r/${transactionTime}". Does not really make
   sense, does it?" The recommendation revised from (a) to (b), words
   only; Frans, 10:00: "OK, do this." Agent f15 (clone f15): the Javadoc,
   harness 6.7's reference and skip list, the entry closed.

   Back to point 1 at 09:58, with e1's report (019-10, section "Can the
   database go on after an Error in a read?"): (c) is possible for an
   `OutOfMemoryError` with two small fixes. Frans, 10:18: "The complexity
   cost is too high. Mainly in future maintenance. I never before tried to
   handle OOM or StackOverflow in Java. In general, this is considered a
   bad idea. So, keep the error model even simpler. I think this is the
   original error model. If the environment is faulty (storage, memory,
   stack), then the database cannot be garanteed to work. Flag this, throw
   exception is called. The user application should close the process."
   (His notes of 2013-01, "Warnings", say the same.) The coordinator
   drafted the model and a proposal in the chat: an `Error` during any
   call or on BergDB's own threads fails the database and is thrown as it
   is; the application ends its process. Frans, 10:31: "Good. Document
   this and implement it. Ensure the Javadoc is clear about this." Agent
   i10 implements it (019-10, clone i10). And: "I would like a clear place
   to put database design information like this. [...] We could look at
   it wholistically after 2026.3." Registered as 017-07, section 4.
4. 019-30, 019-31, 019-33 (damage a start does not detect). Frans, 10:42:
   "Yes, as recommended. BergDB assumes correct storage. Which makes
   sense. Ensure this is documented in the relevant Javadoc comments.
   However, use of checksums in the stream is also a reasonable design.
   Going in that direction is definitely not for 2026.3. Remember the
   target: bug-free Core. Move the possibility of checksums in the stream
   to a new item in 017. This may or may not be added in some future
   release." The Javadoc's words go to agent i10 (with the error model);
   agent d4 (clone d4): the entries closed, harness 6.1, the known
   limitation, 017-08 "Checksums in the stream", 019-07 moved there.
5. 018-04, section 6, Q1 to Q5 (the Pub API's unclear Javadoc). Frans,
   10:58: "Q1, as recommended. Q2, let's go through this one in more
   detail. Q3, tell me more. Q4, expand a little [...] Q5, as recommended."
   After the details (Q2's options (a) document, (b) freeze anew from the
   requested time, (c) each call freezes anew at the latest state: one
   lookup time, set by `setLookupTime(t)` or by `freezeLookupTime()`,
   each undoing the other), Frans, 11:04: "Q2, c, as recommended. Q3, a,
   as recommended. Q4, a, as recommended." Agent p5 (clone p5).

6. 015-86 (gets over 10 ms with 8 readers). Frans, 11:09: "How about
   Option 4 for a later release. Should that be a thing to consider?";
   to the answer (Option 1 now; Option 4, reads wholly in the file
   without `BufferedStream`'s monitor, to 017-07 as reader scaling, to
   measure first), 11:11: "Yes, both. Do it in a new subagent." Agent c6:
   ada8608 (015-86 done, docs/levels.md section 7, `releases/next.md`'s
   limit, 017-07 section 5); README's "Pauses" line by the coordinator
   (db67ca6).
7. W7's rerun (016-10). Frans, 11:21: "Yes." to (A): the flag fixed, all
   five steps in one quiet block on F53 tonight, with a quiet check that
   an idle F53 can pass. Agent w7 prepares it (`/Users/f/fl/bench/016/night4/`).

8. A review of what landed unreviewed. Frans, 11:28: "Item 8, as you
   recommend.": R6 (01b0493, 8e9eccc, c73daba) and R7 (the night's
   concurrency fixes: 015-66, 67, 70, 82, 80), read-only, at xhigh.

### W3. `night.sh` without a fixed time

Frans, 11:21: "By the way, I think we should remove the fixed-time
scheduling of night.sh. You can decide when to run it, right. Like with
other things. What do you think?" To a proposed launchd fallback, 11:25:
"No, no such thing is needed. If we don't plan, we don't code anyway. So
little need for night.sh then. If there are exceptions, I will handle them
manually." Done: the launchd job unloaded, its plist kept in
`/Users/f/fl/bench/launchd-retired/`; agent n1 changed the words (AGENTS.md,
README, docs/levels.md, night.sh's header, 013-01, 013-02, the skill,
docs/log.md). Tonight's plan starts `night.sh` as one of its steps.

Also, Frans, 10:58, on a todo list for 2026.4 ("Is this needed?"): "As
you propose about the todo lists, sounds good": the list for 2026.4 opens
when 2026.3 is released; until then, bounded work for after 2026.3 waits
in 017-07.

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
* 09:58 Agent e1 reported (019-10's new section).
* 10:01 Point 3 decided, (b); agent f15 started.
* 10:08 019-15 done, 5394276 on `main` (`BEFORE COMMIT OK`; harness 6.7's night set OK, its skip list empty).
* 10:31 Point 1 decided: the simple error model; agent i10 to start; 017-07 section 4.
* 10:32 Agent i10 started (019-10, clone i10).
* 10:44 Point 4 decided; agent d4 started (clone d4); i10 told to add "BergDB assumes correct storage".
* 10:57 019-30, 019-31, 019-33 done as decided, 017-08 made, 019-07 moved: ad7187f on `main` (`BEFORE COMMIT OK`; harness 6.1's full sets of seeds 20398 and 20399, 0 failures).
* 11:05 019-10 done, the simple error model: 01b0493 on `main` (`BEFORE COMMIT OK`; harnesses 6.2 and 6.7's night sets). 019-37 registered (i10's find).
* 11:05 Point 5 decided; agent p5 started.
* 11:12 Point 6 decided; agent c6. 11:17 ada8608 on `main`; 11:19 db67ca6 (README).
* 11:21 Point 7 decided; agent w7 started (preparation only).
* 11:22 018-04's Q1 to Q5 done: b13991a on `main` (`BEFORE COMMIT OK`; harness 6.7 now checks all five; its night set OK).
* 11:26 `night.sh`'s launchd job unloaded; 11:27 agent n1 (the words).
* 11:29 Point 8 decided; reviewers R6 and R7 started.
* 11:33 n1's words committed.


## 8. Outcome

Not yet.
