# 006-09 Unattended work, 27 to 28 October 2026

Created 2026-10-27 by Claude (Opus 5.5, Claude Code), at Frans's request.
Status: open. The plan for the unattended work from 2026-10-27, 12:00, to
2026-10-28, 07:00, the progress through the night, and the outcome.


## 1. The request

Frans, 2026-10-27, 11:27: "Unattended work with bergdb/. Please suggest a
plan for work you can do unattented between now and tomorrow at 07:00 am. I
expect a report entry in news.md by then. Add an item to 006 with the plan
you create. Update the item with progress. Go through the items/ to find
tasks to do that you can achieve unattended. Also go through the 005 todos.
While working, feel free to create up to 4 subagents running at a time."

His answers to the draft plan, 11:39:

1. Commits: "yes, do commit." Each gated step on `main`, in his name.
2. 005-51: "yes, put it in java and commit."
3. 005-58: "It is yours."
4. 005-46 and 009: "You decide when to set them to Done."
5. Tonight on F53: "No, only the night.sh testing. This could be cancelled
   for tonight, if you like. So you can run it instead."
6. "Write the plan. Follow BergDB's principles 010."

And at 12:03, to two questions of the plan's first hour:

7. 005-48: if group commit passes the gates, keeps the stream's bytes
   unchanged and measures well tonight, commit it: "Yes."
8. 005-03: if handles removed the sweep it measures, close it as done by
   009: "Yes."


## 2. Ground rules

* **Other sessions.** At 11:30 the session "Startup time" was gating its
  implementation of 005-57 (007-03's step 6) in
  `/Users/f/fl/bench/005-57/`, and the session f1-ce its fix of 005-55 in
  a scratch clone. This work does not touch 005-57, 005-55 or 007-03, and
  their uncommitted edits in the main tree stay as they are. Before code
  that another session's open entry covers is touched, that session is
  asked first: 005-51 changes the eviction thread and `Db.stop()`, which
  005-55 also changes.
* **Clones.** Code and Lean work is done in scratch clones; the main tree
  only takes finished, gated changes. Shared files (`items/005-todo/readme.md`,
  `docs/log.md`, `docs/levels.md`) get targeted edits, and a commit takes
  only this work's hunks, never another session's uncommitted edits.
* **Gates.** A change to `java/` is committed after `java/before-commit.sh`
  prints `BEFORE COMMIT OK`, and the level script of the mechanism it
  changes (`level4.sh` for 005-51). A change to `lean/` after `lake build`
  is clean, with no `sorry` and no new axiom.
* **Commits.** In Frans's name only, with no AI attribution; this session
  makes them, also for its subagents' work.
* **Timing.** Timed runs only in the quiet block (section 5), on an F53
  with no other JVM, build, gate or Lean, and with this session idle.
  Byte counts, memory and other deterministic measurements may run at any
  time. s1 is checked with `ps` before each run.
* **Subagents.** At most 4 at a time, each in a clone of its own, each
  with a brief that points to its 005 entry and to this file.
* **News.** `tools/news.sh` as work finishes, fails or needs Frans; a
  summary entry by 07:00.
* **Principles.** Section 4.


## 3. The work, in order

### W1. 005-46's measurements, to close 005-46 and 009's target 2

005-46 is in the code (`eaec93e`); its "Done when" leaves the
measurements, and 009's target 2 (no stop-the-world of BergDB's own longer
than about 20 ms) waits for them.

1. The entry's probes again on the new code, on F53: no reader's longest
   read follows the forces, the new files or the cut; in `SlowForceProbe`
   no get and no single-put commit waits for a slow force.
2. The pause probe on s1 (009-03's `s1-probe`, `run-pp2.sh`): no get
   waits for a force; the report sets the longest commits beside the
   writer's waits for room and the forces. This afternoon; s1 was idle at
   11:30.
3. P4's soak under ZGC on F53 (009-04's soak, about 50 minutes): the cuts
   are no longer its slowest commits and reads (009-04, section 7.3).
4. Props (CORE) and 009-03's ScaleBench block from the OS's cache (C) on
   F53, against `bf19075` (before 005-46) in turns: no fewer reads a
   second.

Then the results in 005-46; if its "Done when" is met, 005-46 is set done.
009 is set done if nothing else of 009-01's "done" is left; otherwise its
log says what is.

### W2. 005-49, smooth index writes

The next step of 007 after step 6 (005-57): 007-03's deadline (step 3)
follows 005-49's recommendation. An investigation; nothing goes into
`java/`.

1. Extend 005-38's `WriteBench` (`38-writes-at-scale/wb/`) to record each
   record's index bytes and puts; rerun the update phase of 005-38's
   `run3.sh` at 10M keys, sd 200 and 1000 MB. Byte counts, so any time.
2. Question 1: the distribution of a record's index bytes against its
   puts.
3. A paced take, prototyped in a clone: each record takes index nodes in
   proportion to its own size, counted in bytes or puts, never in time;
   the deadline stays the backstop. Measured against today for the total
   bytes, the largest record and the startup section.
4. The report, a subitem of 005-49, with a recommendation for 007-03's
   step 3.

### W3. 005-58, a Lean theorem for rule 4 by position

On the states that the model's startup reaches, a pointer of D whose node
has a canonical object names a version of the startup section, the
version before one, or the canonical object's own; so rule 4 by position
(005-57) is rule 4 by node id (`HMem.linkD`). First the statement in the
model's terms and what it needs (questions 1 and 2), then the proof.
Committed in `lean/` when `lake build` is clean. 005-57's report and
`docs/levels.md` cite it once the session "Startup time" agrees, as both
have its uncommitted edits.

### W4. 005-51, eviction only in response to the calls

The eviction thread waits with no timeout and wakes only on a call's
request; `stop()` and `close()` wake it, and it ends at once. A test that
an idle database's threads do not wake; `before-commit.sh` and
`level4.sh`; committed. After or with 005-55 (f1-ce), which changes the
same thread's hold on the `Db`.

Then the rest of 010-P3's list, measured with 005-14's `procstat.c`
(`proc_pid_rusage`): an open, idle database after loads and commits wakes
no thread of BergDB's own, the replica's consumer included (005-14 saw it
wake twice a second). A departure is registered in 005 and listed under
P3 in 010-01.

### W5. 005-48, group commit

A prototype in a clone: `flushSoon()` in `BufferedStream`, called by
`StorageManager.sync` and `syncStrong`, so that a sync that waits starts
the flush instead of waiting for the buffer timer. The durable-commit runs
of `performance-bufftime.suite` at 20 ms, against HEAD, on F53 (in the
quiet block, in turns) and on s1; questions 1 and 2 answered and a
recommendation in 005-48. Nothing goes into `java/` before Frans says go
(005-48, "Done when").

### W6. If there is time, in this order

1. 005-53, question 3: a reading of `Reclaim` and `Db`'s start, which may
   find a fault of its own.
2. 005-03: is the sweep it measures gone with 009 (`docs/levels.md` speaks
   of it in the past)? If so, closed as done by 009, with 009-03's
   measurements as the evidence; if not, restated.
3. 005-56: a script that checks each package's imports against its
   `package.html` list, and the mismatches.
4. 005-52's first step, in the quiet block: the budget lowered by
   `setBudget` in the middle of a ScaleBench run; the eviction thread's
   work and the longest waits of gets and commits until the resident
   bytes reach it.
5. 009's ScaleBench at 10M keys in Shenandoah's default mode (about 35
   minutes), only if the block has room: a recommendation of a collector,
   no longer target 2's evidence.

### Not tonight

005-05, 005-11 and 005-47 are decisions for Frans. 005-06, 005-07 and
005-54 come after the work above. 005-55 and 005-57 are other sessions'.
007-03's steps 2 to 4 wait for 005-49. 006-06 is a note for discussion.


## 4. The principles (010)

Each piece of work is checked against 010-01; a departure that a change
must make is documented there, under its principle, as Frans's rule for
the principles says. Across all of it: no new setting (P10), no global
state (P9), no new timer or polling thread (P3), and the simple solution
first (P11).

| Work | Principles | What they ask of it |
|---|---|---|
| W1, 005-46 | P1, P7 | BergDB's own waits at most about 20 ms, readers included; a failed delete fails the stream at its next operation |
| W2, 005-49 | P4, P1, P5, P2 | A commit's index writes in proportion to its own size; the pacing counts bytes or puts, never time, so the stream stays deterministic; the startup section stays bounded, the deadline the backstop |
| W3, 005-58 | P5 | Rule 4 by position, the fix of a cold start's random reads, proved to link what rule 4 by node id links |
| W4, 005-51 | P3, P8 | No wake-up that no call asked for; eviction's work follows the calls, so runs repeat |
| W5, 005-48 | P3, P2, P1 | The sync call starts the flush: work in response to a call, no new thread or timer; the stream's bytes unchanged (StreamDigest identical); no commit waits longer |
| W6 | P6, P12, P1 | 005-52 and 005-53: changes while the database runs, in steps; 005-56: a small Core Layer that depends on nothing above it; 005-03: no stop-the-world |


## 5. Timeline

Times in CET. `night.sh` stays at 02:10 (changed at 12:15 from the first
version of this plan, which moved it by hand to 21:30: launchd is left as
it is, and the block needs no step of this session), so the quiet block has
two windows: 22:30 to 02:05, and from `night.sh`'s end (about 03:00) to
06:15.

| Time | What |
|---|---|
| 11:30–12:00 | The plan with Frans; this file |
| 12:00–19:00 | W2, W3, W4 (after 005-55) and W5's prototype in clones, up to 4 subagents; W1.2 on s1; W1.1 if F53 is quiet |
| 19:00–21:30 | The gates on the combined tree; commits; W6.1 to W6.3 |
| 21:45 | CPU-heavy work stops; the conductor's steps checked |
| 22:30–02:05 | The quiet block's window 1 on F53, this session idle: W1.3, W1.4, W5's runs, W6.4 (and W6.5) |
| 02:10–03:00 | `night.sh`, from launchd, as every night |
| 03:00–06:15 | Window 2, for the steps that did not fit in window 1 |
| 06:15–07:00 | Write-ups, commits, the status of 005-46 and 009; this file's outcome; the summary in `news.md` |

Lean and builds stop before the quiet block; a subagent still working at
21:45 is stopped, and its state is written in its entry.


## 6. If this session stops

A usage limit can stop this session and its subagents for hours. So:

* **The conductor.** The quiet block is run by
  `/Users/f/fl/bench/006-09/night/conductor.sh`, started at 12:15 with
  `nohup` and `caffeinate`, outside this session: it runs the steps in
  `steps.txt` whose script has a `.READY` marker (written by whoever
  prepared it, after a smoke test), one at a time after a quiet check, in
  the two windows; it writes `results.txt`, `conductor.log` and one
  `news.md` entry when the block ends. At 06:50, if this session has not
  written its summary (the marker `summary-written`), it writes a short
  one itself.
* **Check-ins.** Scheduled prompts of this session resume the work after a
  limit: every hour from 12:17 to 21:17 (resume stopped subagents, carry
  on with the timeline), 21:41 (prepare the block), and 05:57, 06:27 and
  06:44 (the morning's write-up and summary, the later ones shorter).
* **State.** This file's progress section, and the entries' own files.
  Subagents write their state into their entries as they go.


## 7. Progress

2026-10-27, 11:45. The plan written, from Frans's answers of 11:39, and
committed (`5ca72dd`). Four subagents started, each in a clone of its
own: W1, W2, W3 and W5.

2026-10-27, 11:50. The other sessions: f1-ce's 005-55 is in (`cec0032`),
so W4 started on it, in this session. The session "Startup time"
committed 005-57 (`07b6375`), has no timed runs planned today or tonight,
and agreed that 005-58 is cited in 005-57's report and `docs/levels.md`
when it is proved. The session f1-02, which made 005-46, had Frans's go
for its remaining checks: it runs W1.1 (the probes on F53) and W1.2 (the
pause probe on s1, `bf19075` and `cec0032` in turns, G1 and ZGC) this
afternoon and writes them into 005-46; W1.3 and W1.4 stay in the quiet
block, prepared by this work's W1 subagent, and the status of 005-46 and
009 is decided here.

2026-10-27, 12:12. W4 and W6.2 done and committed: 005-51 (`c2aab10`; the
eviction thread waits with no timeout, the close ends it; a unit test that
fails on the code before; `before-commit.sh` and `level4.sh` full pass)
and 005-03, closed as done by 009 (`4f7cd60`). f1-02 committed 005-46's
measurements of the afternoon (`12d7ec7`): after the change no get waited
for a force on s1, and on F53 every probe's verdict held by a wide margin;
the maxima of 10 to 30 ms under the afternoon's load are for the quiet
block to confirm.

2026-10-27, 12:15. At Frans's request ("Ensure you can continue to work
even if you run out of 5h Claude session usage."): the night conductor
started and the check-ins scheduled (section 6); `night.sh` left at 02:10.

2026-10-27, 12:19. Frans chose to close 005-46 on the afternoon's
evidence (f1-02, `1f1e542`). Tonight's soak, Props and ScaleBench are a
confirmation: 005-46 is reopened if they show a read or a commit waiting
for the stream's writer; they are also 009's evidence for target 2.

2026-10-27, 12:30. W1's three steps for the block are ready (soak, Props,
ScaleBench C); W1 now prepares a fourth (`performance.sh ab` against
2026.1) and reruns 009-03's ScaleBench from the device on s1 on HEAD. W3
reported its theorems proved; at Frans's word ("max for Lean") a new agent
at max effort reviews and finishes 005-58. Usage paced at Frans's request
(68 percent of the 5-hour budget used, a reset at about 14:30): W2 and W5
paused at safe points until 14:38; then, at his word ("In general, I like
to use Opus 5.5 at High or Max effort levels. Max when the problem is
hard. [...] I want 005-49 to use Max"), W2 and W5 go on as new agents at
max effort. W5 found that `level3.sh`'s ReclaimReaders failed once in 15
runs with group commit (none in 15 without), probably a race in the test
that faster syncs expose; to be understood before any commit.

2026-10-27, 12:35. 005-51's idle measurement: with the eviction thread
started, an idle database wakes no more than the JVM; the thread used 1.4
ms of CPU a minute before, none after (005-51, Outcome).

2026-10-27, 13:20. W3 done: 005-58 proved and committed (`7c1ce2f`, the
Lean files; `0965377`, the entry, the citations in 005-57's report and
`docs/levels.md`); the review at max effort found the statements true and
not vacuous, with one limit written in the entry (the model's startup
links by node id where Java uses `posToId`, so those branches are proved
but not exercised by the model's runs). For Frans: the trusted additions,
and the by-id check in `linkToCanonical` (recommended: it stays).

2026-10-27, 13:30. W1 done: the quiet block's four steps of 005-46 and 009
are ready (`night/soak.sh`, `props.sh`, `scalebench-c.sh`, `perf-ab.sh`,
the last `performance.sh ab` against 2026.1, 009-01's done item 7), and
009-03's ScaleBench from the device ran on s1 on HEAD (009-03, section 9):
no reader waits on a file's monitor any more (10.7 percent of samples
before 005-46), 15 to 32 percent more gets a second with 2 and 4 threads;
the longest gets, 64 to 74 ms, overlap nothing of BergDB's (s1's disk, and
G1's young collections under G1); one get of 2,760 ms with nothing else
running, put down to s1's disk or the kernel's reclaim in the run's memory
cgroup, a judgement for Frans to see. Cold startup at 10M keys: 21.6 and
19.6 s (170 to 193 s before 005-57).

2026-10-27, 14:38. The work resumed after the usage window's reset: W2
(005-49) and W5 (005-48) go on as new agents at max effort, from their
State notes, clones and outputs. Two agents for now, to pace usage; W6
(005-53's question 3, 005-56's check, 005-52's night step) waits for a
free slot.

2026-10-27, 14:45 to 15:22. Both agents stopped at the usage limit (its
window reset at 15:20, not 14:30). At 15:22 Frans: "5h usage has been
reset. At 0% now. So, go ahead." Both resumed where they stopped, and W6
started (at high effort, as its pieces are small): 005-53's question 3,
005-56's check, 005-52's night step.

2026-10-27, 15:45. W6 done (`4f38f52`): 005-53's question 3 found a small
fault (Reclaim keeps the builder's startup distance); 005-56's check lists
7 mismatches; 005-52's night step ready.

2026-10-27, 16:15. W5 done: 005-48 in the code (`e611709`, entry
`78a8d38`); the level3 failure was a race in ReclaimReaders's check, also
without group commit, fixed there; on s1 one thread's durable commits went
from 38 to 213 a second; the stream's bytes unchanged. F53's runs tonight.

2026-10-27, 16:38. Frans on 005-58's questions: "1. As recommended. 2. As
recommended." (`ed852ad`).

2026-10-27, 16:45. W2 done: 005-49's report recommends a paced take for
007-03's step 3 (`374f744`). Frans chose three more pieces for the evening
("Fix 005-53's Reclaim fault", "007-03 step 2: debt test", "Draft 009's
closure"): W7, W8 and W9, at high effort.

2026-10-27, 17:10. W9's draft of 009's closure is ready (two patches and
notes in [09-unattended-27-28-october/](09-unattended-27-28-october/)), to
be applied in the morning after the soak. W7 done: 005-61, Reclaim spaces
its iterations by the database's live startup distance (`a175840`,
`7fde735`). Frans on 005-49's questions: the setting is the section's
target, the actual startup distance what a start reads from; the default
stays 50 MB (`82b59a1`).

2026-10-27, 17:28. Frans chose three more pieces for the evening: 007-03's
step 3 as a patch for his review (W10, max effort; not committed to
`java/`), 005-59's option A (W11), and T9 and T12 over handles in Lean
(W12, max effort, a new 005 entry). Four agents with W8.

2026-10-27, 17:40. W11 done: 005-59, option A (`f9c3b09`, `2eaaa45`).

2026-10-27, 18:40. W10 done: 007-07, step 3 as a patch for Frans
(`49f99a1`; not in `java/`). Found on the way: `level2.sh`'s step 6
(BryanRepro) failed on `main` from `eaec93e` (005-46) on.

2026-10-27, 19:12. W13: the test started a database right after `stop()`
while the old one's cut thread still deleted files; no data at risk; the
test now uses `close()` (`b0661ba`, level2 full passes); the API question
registered as 005-63 (`9fa1789`).

2026-10-27, 19:39. W12 and W14: T9 and T12 over handles proved and
reviewed at max effort, in `main` (`bba91dd` to `a506b34`, entry
`422fad4`); what to remove of the old design is for Frans. W8, 007-03's
step 2, still runs.

2026-10-27, 20:42. W8 done: 007-06, step 2 of 007-03 (`c143402`). All
agents done. The quiet block's steps are ready (READY markers): P4's soak,
Props, ScaleBench C and `performance.sh ab` (005-46, 009), 005-48's F53
runs, 005-52's budget step; 005-48's s1 runs ran in the afternoon. The
conductor waits for 22:30.

2026-10-27, 21:41. Before the block: no agent, build, gate or Lean runs;
the conductor is alive, its six F53 steps READY with their minutes (soak
115, Props 12, ScaleBench C 65, 005-48's runs 60, `performance.sh ab` 40,
budget 45), 005-48's s1 step done. This session is idle until the
morning.


## 8. Outcome

Filled in by 07:00 on 2026-10-28.
