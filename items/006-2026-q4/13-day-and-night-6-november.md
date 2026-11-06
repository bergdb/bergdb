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

9. Behaviour changes in `releases/next.md` (015-55, 015-57, 015-41's
   touch of the experimental object path). Frans, 11:33: "Yes." to keep
   all three.
10. "Built by Claude" in the headers of 018-02, 018-04 and 018-07.
    Frans, 11:35: "As recommended.": (b), the lines moved to each item's
    Log; done by the coordinator.

### W2b. Towards 2026.3's "Ready"

Frans, 11:36: "Overall where are we on the work towards release 2026.3
-- a bug-free Core? Can we finish today or tonight?" The answer: not
tonight; the known Core faults by tomorrow morning, a release candidate
tomorrow (or Sunday or Monday with what the reviews and harness 6.6
find). Frans, 11:46, on harness 6.6's scope: "As you recommend.": Option
1, the 8 jcstress tests of `java/stress/jcstress/` rerun on today's code
on F53 and s1, and tests added only for the shared fields that review R7
flags. And: "Can we speed things up? More subagents? Use High as effort
level for subagents from now on. To preserve usage." So: up to 6 agents
at a time, at high; gates one at a time under a lock
(`/Users/f/fl/bench/006-13/gate.lock`).

Review R6 (11:44): 01b0493, 8e9eccc and c73daba without A findings;
B1 to B3 and C1 to C9 registered as 019-38 (index jobs fail the database
on an interrupt, an expiry or a refusal: a regression of today's change),
019-39 (hangs in the error path) and 019-40 (the C findings).

Review R7 (11:55): the night's concurrency fixes 015-66, 67, 70, 82 and
80 OK, no A finding, no lock-order cycle; its B1 is 019-39's B3,
confirmed by a run; C findings registered as 019-41, with C4 a line in
019-36 and C5 in 019-40. No shared field needs a new jcstress test.

### W4. Release 2026.4: a bug-free database

Frans, 11:58: "I would like to discuss next release, 2026.4. The overall
theme is: a bug-free database. We add the non-Core part of the database
covering all functionality available to a user of it. Including indexing,
and serialization of Java objects." To the proposed first step (an
inventory, keep, simplify or drop per feature) and two questions, 12:05:
"Create a new item for it. nnn-release-2026-4. I like your plan. Start
the agent now." "No, nothing in particular is off the table. No need for
any backwards-compatibility. API can change." User indexes: "Yes. That is
included." Done: 020-release-2026-4 (92844c2); agent v1 writes 020-01.

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
Changed at Frans's request, 15:51: "I would like us to start preparing
for 2026.4 work. I would like a new todo list for this work." 021-todo
was created (19b8ad1); 019 keeps 2026.3's entries until that release.

### W2. KISS as a principle

Frans, 09:47: "Also, add KISS to our principles 010. Keep it short and
simple. Always important. Also with AI, even though more complexity can be
sustained now." Done: 010-P13, "KISS".


## 4. The principles

010's: P1 (no stop-the-world in BergDB's own code, about 20 ms), P7 (a
database whose environment has failed, or that has a bug, does not run
on), and P13, KISS (Frans, 09:38 and 09:47).


## 5. Timeline

Frans, 12:14: "I am about to go soon. Is your plan for working unattended
in place? [...] From now on I expect to check in occasionally during the
afternoon. Likely from my mobile. I expect a morning report by 07:00 with
the status of the unattended work session. [...] Hopefully release 2026.3
can be made tomorrow in the morning. That is our goal. Use up to 90% of
the available Claude usage." Unattended from 12:20 to 2026-11-07, 07:00.

* **Until 20:15, the day's fixes land** (each gated, under the gate lock):
  019-32 (f32), 019-39 (i39), 019-41 (f41), then 019-40 (R6's C
  findings); 019-36's fix if q1's s1 measurement shows waits over 20 ms
  and it can land in time; the documentation read through (d30, Ready
  4); harness 6.6's jcstress run on s1 (j66). The inventory 020-01 (v1,
  xhigh) is for 2026.4 and lands any time (items only).
* **15:00, an early `night.sh`** (the normal run, about 50 minutes) on
  `main` under the gate lock (`/Users/f/fl/bench/006-13/night/early.sh`),
  so that the day's landings are tested hours before the candidate
  (Frans, 12:35: "Should we start with a faster set of tests to catch and
  fix bugs from that first?").
* **20:15, `main` frozen** for the release.
* **About 20:30, the release candidate** (018-09, agent r30's scripts):
  commit A (`BuildInfo` at 2026.3), the jar, its tests on F53 with JDK 27
  and 17, s1's chain, StreamDigest against 2026.2's decided digests.
* **20:45 to about 02:45, `night.sh large`** on `main` under the gate
  lock (`/Users/f/fl/bench/006-13/night/chain.sh`, started 12:15), then
  jcstress on F53 (harness 6.6).
* **02:00 to 06:00, block-q** (q1's script; it waits for the chain): 019-36
  measured on F53, then 019-35's pairs. W7's rerun moves to another night.
* **06:00 to 07:00, the morning**: the results into the items, this plan's
  Outcome, a summary in `news.md`, the report to Frans by 07:00.
* **At Frans's word**: R8 and R9 (the files of `releases/2026.3/`, commit
  B and the tag `release-2026.3`, local), about 30 minutes.

Frans, 12:31, on the defaults: 019-35 "traced tonight but not blocking
[...]": "Agreed." On a fault found tonight: "If the bug is in Core,
register it and fix it to your best ability. Do not wait for me." So a
Core fault found by `night.sh large` or jcstress is registered and fixed
at once (gated, outside the quiet block, 02:00 to 06:00); the release's
commit is then made again from `main` in the morning, with `night.sh` on
it (about 45 minutes; `night.sh large`'s 6 hours do not fit), and the
morning report says what ran on which commit. 019-36 is not a fault
(Frans, 12:28): its figures are for a later decision.

Check-ins every 20 minutes from 06:00 to 01:59; none from 02:00 to 05:59
(the quiet block). The watchdog runs to 07:00. Agents at high (v1 at
xhigh); at most about 6 at a time, more when some only wait for their
runs; usage up to 90 % of the week.


### For Frans to decide (in the morning)

1. From d30's read-through (12:44), not fixed: `DataFormatException`
   belongs to the object code but is not marked experimental (W1's list
   is Frans's); lean/README.md holds about 740 lines of dated progress
   log (AGENTS.md: logs belong in an item), two tables with rows up to
   1,500 characters, "Written by Claude" in its line 4 (sis-model.md the
   same; as for 018-02's header, 006-12's point 10), TakeCheck that no
   longer compiles (015-03), and sistest, phystest and reclaimtest run by
   hand only; dated history sentences in the user Javadoc; `Time.utc` and
   `resolve` do not document `BadFormatException`. Recommended: after the
   release; the "Written by Claude" lines as point 10's (b).
2. From 019-44 (13:19): a String inside an object (the experimental
   object code) still gets '?' for a lone surrogate, as
   `DbObjectTester.testLoneSurrogates` (005-26) requires; a String value
   and a key now refuse it. Recommended: refuse it in objects too, in
   2026.4 (020), with F1's closed list of types.
3. 019-40's C8 (35f5b72): the start's check of a meta block's last
   transaction is now the invariant itself (between the stream's first
   position and the block), a tighter check landed the night before the
   release; tonight's `night.sh large` starts many databases.
   Recommended: keep it, if the night is clean.

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
* 11:35 Points 9 and 10 decided; 006-12's list done. Agent f32 started (019-37, then 019-32).
* 11:44 Review R6 done; 019-38, 019-39, 019-40 registered.
* 11:47 Agent w7 done: tonight's block `/Users/f/fl/bench/016/night4/block.sh` ready and rehearsed (quiet check: load below 2.5 twice; not started).
* 11:48 Agents i38, i39, j66, f06 started (high).
* 11:50 019-37 done: e7102b2 on `main`.
* 11:55 Review R7 done; 019-41 registered; agent f41 started.
* 12:00 i39: a full heap in a fresh JVM can still hang a sync (first CAS links); the coordinator: no warming (Frans, 10:18), a sentence on the limit instead.
* 12:02 019-38 done: cecaf4c on `main`. Agent q1 started (tonight's block for 019-35 and 019-36).
* 12:07 020 created; agent v1 started (020-01).
* 12:08 v1 restarted at xhigh (Frans, 12:07: "This is important.").
* 12:15 Unattended set up: the night chain (night.sh large at 20:45, then jcstress on F53), the watchdog to 07:00, check-ins; agents r30 (the release's scripts, 018-09) and d30 (the documentation, Ready 4) started.
* 12:16 015-06 done: 4248141 on `main` (`BEFORE COMMIT OK`, LEVEL 2 OK).
* 12:19 Harness 6.6 on s1: 8 of 8 jcstress tests OK (018-08, 2691750).
* 12:24 019-39 done: 940e603 (LEVEL 2 OK). Agent i40 started (019-40).
* 12:28 019-36 made an Investigate (Frans: performance, not a fault; 727c8d3). 020-01 done (e8ab9ae); its N1 (an index build bricks a database since 019-10) registered as 019-42 with the coordinator's default (b); agent f42 started.
* 12:30 019-41 done: 8f0d117 (LEVEL 4 OK).
* 12:31 Frans: a Core fault found tonight is fixed at once, without waiting for him.
* 12:33 Usage tight (5-hour window 76 %, reset 13:10): no new agent until then.
* 12:35 019-43 registered (r30's rehearsal: harness 6.2's sample flaky on s1 with JDK 17); its agent at 13:13.
* 12:36 Early `night.sh` scheduled for 15:00 (Frans, 12:35).
* 12:38 019-32 done: 00b184e (LEVEL 2 quick OK).
* 12:42 019-42 done: e687400 (gated on the combined tree).
* 12:44 d30's read-through done (1dde232, landing as 6a7d6f4 after a merge of `releases/next.md`); its four small Pub API faults registered as 019-44; the rest for Frans (above).
* 12:48 The documentation landed: 8996de0. 12:56 019-40 done: 35f5b72. 12:57 018-09, the release's plan (r30), committed: the candidate scheduled for 20:14. 13:03 q1 done: block-q started (it waits for 02:00); 019-36 on s1, longest wait 19.85 ms.
* 13:14 Agents f43 (019-43, the blocker) and f44 (019-44) started.
* 13:16 f43: 019-43 is the harness's oracle (a read racing the stop's close), being checked that nothing a user sees says "failed".
* 13:20 019-44 done: a9da30c.
* 13:35 019-43 done: b63273d, harness 6.2's oracle, not the Core (a read that the stop's close overtook; nothing a user sees reports it; the Core unchanged); loops of 100 runs on s1 (JDK 17, 27) and F53 (JDK 17) clean. 019's open entries are now 019-35 and 019-36 only, both Investigate: no known fault of the Core is open (018-01, "Ready", 1), pending tonight's runs.
* 15:00 The early `night.sh` started on 3aa2d93.
* 15:52 021-todo created for 2026.4 (Frans, 15:51).


## 8. Outcome

Not yet.
