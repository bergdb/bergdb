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


## 3c. The night of 9 to 10 November

Frans, 12:56: "go", to the coordinator's defaults: he is back at 07:00;
coding until 21:30; the freeze 21:30 to 22:00 (the last gate on main's
head is the candidate; main pushed, without tags); the night as below;
the summary by 07:00 in `news.md` and section 6; no tag. Changed at his
word, 13:02: the candidate is cut at 20:00. The freeze is 19:30 to
20:00 and the candidate is main's head at 20:00; from 20:00 to 22:00
only `items/` commits land (022's C coding) and `java/` stays frozen;
the quiet block still starts at 22:00.

The night runs by itself: a conductor (013-01, section 7), started with
`nohup caffeinate -i` at 13:15 (pid 2419), waits for 22:00 in
`/Users/f/fl/bench/2026-11-09/night/` (N below). N's `README.md` has
the details: the times, the outputs and how to stop. The coordinator is
idle from 22:00.

**The freeze, 19:30 to 20:00, by the coordinator.** After the last
landing in `java/`: `sh N/freeze.sh` (4 to 6 minutes). It clones main's
committed HEAD into `N/candidate/` and records it (`candidate/COMMIT`,
`commit.txt`), gates it (`before-commit.sh` under the gate lock), builds
the tests' jar and the users' jar (`bergdb-release.jar`), compiles the
jcstress tests and StreamDigest, builds the Lean model, and writes the
READY markers of the steps that use the candidate. It prints `FREEZE
OK`. Then main is pushed, without tags.

**The quiet block, 22:00 to 06:15 on F53.** One step at a time, in this
order (Frans's), each after the quiet check and only if it ends by 06:15:

| Step | What | Expected | About |
|---|---|---|---|
| 1 | `night-large.sh`: `night.sh large` on the candidate | 6 h 15 min | 22:03 to 04:20 |
| 2 | `jcstress.sh`: the 8 jcstress tests, default mode (harness 6.6) | 5 to 10 min | to 04:30 |
| 3 | `checks.sh`: StreamDigest against 2026.3, the Lean axioms | 1 min | to 04:35 |
| 4 | 022's `step5.sh`, BUDGET the minutes left less 5, at most 120 | about 90 min | to 06:10 |
| 5 | `props-006-16.sh`: 006-16's CORE rounds, DEADLINE 06:00 | 40 min to 2 h | if time |
| 6 | 022's `step6-2026-4.sh`, 2026.4's long runs (READY by 022) | 90 min | if time |

**s1, from 22:00, beside them:** `s1-jartests.sh`, the tests on the
candidate's jars with JDK 27 and 17, as for 2026.3 (018-09, step R5):
Unit, F and Night from the tests' jar, and 018-09's user program
compiled and run against the users' jar alone; about 50 to 70 minutes.
StreamDigest and the axioms ran on F53 for 2026.3, so they are step 3.

**On the candidate.** Every step runs on the commit that freeze.sh
recorded. `night.sh` takes no commit: it clones main's committed HEAD.
So step 1 checks that main's tree outside `items/` equals the
candidate's (`git diff --quiet CANDIDATE HEAD -- . ':(exclude)items'`).
If main's code moved after the freeze, it runs the candidate clone's
`night.sh` instead, which clones the candidate itself. After the run it
checks the report's `Commit:` line the same way. The other steps take
the jars and classes from `N/candidate/` and compile nothing.

**Time.** `night.sh large` took 313 minutes on 2026-11-06. With the
steps added since (lean-tests, longer night tests, harness-soak, fuzz,
kill-restart) it is about 6 h 15 min. So about 100 minutes are left
after step 3. 022's step5 says 120 minutes. Its line in `steps.txt` has
a least of 60: it starts with BUDGET, and step5.sh runs the parts that
fit, in its order. Steps 5 and 6 run only if `night.sh large` ends
early. 006-16's `2026.4c` build is f3af680, not tonight's candidate.

**Markers.** A step runs only with its `.READY` marker, written after a
passed smoke test. The smoke tests ran 13:05 to 13:20 against a build
of main 82edabf in `N/smoke/`, without timed runs. The markers:

* by n09: `night-large.sh` and `props-006-16.sh`;
* by freeze.sh, after its build: `jcstress.sh`, `checks.sh` and
  `s1-jartests.sh`;
* by the 022 session: `step5.sh` (13:08), and step6's by 21:45 (its
  line in `steps.txt` is a placeholder).

The conductor writes `.DONE` after each step; the markers are removed
in the morning.

**Outputs.** In N: `results.txt` (each step's exit code, minutes and
whether it ran quiet), `conductor.log`, `status.txt` and
`out/LABEL.txt`; `night.sh`'s report in `java/build/night/`. In
`news.md`: `night.sh`'s entry, 022-step5's (the last line of
`/Users/f/fl/bench/022/out/night/run.log`), and the conductor's at
06:15. At 06:50 the conductor writes a fallback entry if
`N/summary-written` is missing; the coordinator touches it after its
summary.


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

Written by coord-1109 on 10 November, 06:40. The day's events, agent by
agent, are in `/Users/f/fl/bench/coord/2026-11-09/state.md`.

### 6.1. The day

* About 60 faults fixed on 9 November, every one with a failing test
  first, gated, the Core's with `level1.sh` and an independent review;
  about 80 Javadoc corrections. Batches 1 to 44 on `main`; the candidate
  `03ce6ec` (gate, JAVADOC PUB, LEVEL 1 OK; frozen at 19:03, FREEZE OK),
  pushed without a tag; since then only items.
* What found the faults: the AI-user applications (020-24, 18 in 6
  rounds; 006-20) found the most, then the C port (022's test ports and
  three black-box C users), then Codex at max (5 rounds). Kill-restart
  (2,993 kills), fuzzing, the harnesses' long runs, SpotBugs and TLA+
  (020-26) found little. Frans, 19:20: the C port and AI-user testing
  were the most productive tools.
* Lean: 020-29 proves 020-26's safety invariants for every size, and
  liveness (on its branch).
* Decisions applied: encryption out of 2026.4's API (020-28; 017-10);
  the Core API's nulls and ranges (020-27); Android in scope; misuse of
  the API ends in an exception (021-21, 021-22).

### 6.2. The night (section 3c), on the candidate `03ce6ec`

| Step                  | Result                                                       |
|---|---|
| `night.sh large`, F53 | NIGHT OK, 396 min (started 22:30, not quiet); MEM 129        |
| jcstress, F53         | 8 of 8 OK                                                    |
| checks, F53           | digests identical to 2026.3's (48 of 48); axioms OK          |
| s1 jar tests, JDK 27  | unit 1,625, f 86, night 26, user program: all OK             |
| s1 jar tests, JDK 17  | unit, night, user program OK; f: 1 of 86 failed (below)      |
| 022-2026.4, 022-step5 | not run: did not fit after 05:40                             |
| props-006-16          | not run: did not fit                                         |

The JDK 17 f-test, `FileStreamPowerLossTester.testSyncDoesNotAdvanceAfterFailedFileForce`,
got `DirectoryInUseException` on a temporary directory it had just made.
An agent found the cause by 06:25 (report
`/Users/f/fl/bench/2026-11-10/jdk17-f/report.md`): a race, not a leak.
The test before it returns while its `FileStream` is still being closed
on the storage's thread (its `stop()` does not wait for a failed
storage) and deletes the directory; `FileStream.unlockDir()` closes
`bergdb.lock` before it removes the key from its set of locked
directories, and in that moment ext4 gave the next test's new directory
the same inode. Reproduced on s1 with JDK 17 and JDK 27, about 1 in
1,000. Test hygiene first; behind it a small race of the product that
can refuse, rarely and on Linux, a start in a new directory right after
a database was stopped and its directory deleted; a retry works; no
wrong or lost data.

The long run on s1 of 9 November (020-17, soak6, the morning's code),
which nobody read that evening: 8 FAIL and 6 TIMEOUT of 363 jobs,
triaged on 10 November (020-17, section 6.1): faults of the harness and
settings below the API's least, and one status lag of BergDB (low).

### 6.3. For Frans to decide (most urgent first)

1. **Tag 2026.4 from `03ce6ec`?** The night is clean but for the JDK 17
   test race above, and the soak's findings block nothing. Rec: yes,
   after 2 and 3.
2. **Before the tag: replace `releases/next.md`'s known issue with
   021-25's draft** ("The note for the tag"). Rec: yes; the present note
   understates it (020-24-18, U18-2).
3. **Before the tag: the read-path fix 021-28?** Branch
   `scan-deleted-keys` in `/Users/f/fl/bench/2026-11-09/clone-q34`
   (`2bfeb3e3`, `240f2b3e`, `eebeb39d`): a scan ends at its range's end
   instead of walking deleted keys after it (020-24-17, U17-1: 30.7 ms to
   0.01 ms). No stream change: Codex found the appended bytes and read
   sets identical to `03ce6ec`'s; its round 5 found no high or medium,
   the two lows fixed; gate OK, level1 OK. Rec: yes; then a new
   candidate with the gate, level1, level3 quick and the s1 jar tests.
4. **021-25 fixes (a) and (b) in 2026.5** (decided 19:17). Fix (a)'s
   prototype (branch `021-25-fix-a`) brings the cuts back but does not
   bound the database; (b) is the fix, also for 020-24-16's U16-1.
5. **The night's new findings, for 2026.5:** the JDK 17 test race (the
   test closes and waits; `unlockDir()` removes the key before it
   releases the lock); 020-17's H3-O5 (the job ACTIVE under the lock),
   H2-O5 and H2-O6 (harness). Rec: one 021 entry each for the two of
   BergDB.
6. **022's night steps** (`runs-2026-4.sh`, 90 minutes, and `step5.sh`)
   and props-006-16 did not run. Rec: today on F53 when it is free.
7. **Merge 020-29's branch** (a new Lean library `BergDB` in `lean/`):
   when?
8. **021-22's change of behaviour:** a `Connection` shared by threads for
   writes now throws (it was forbidden, and it worked). For the release
   notes as it is?
9. **For 2026.5 and later** (020-11, section 11 has the list with
   references): the long-key quadratic loop (021-16 Q1, U2-3, U1-1);
   021-27 option A; U8-1 and U2-6 (deleted or cut stream files); U2-8;
   U2-2; U13-7; the index manager's lock fairness (020-29); `rw()` on a
   hot key (U16-2); 017-10 encryption; the Core API's Javadoc (x28 Q1);
   U15-6, U3-6; U10-2; the applications' API wishes.
10. **Two unit tests wait without a timeout** (`PubTester.java:720`,
    `PubTesterOutput.java:188`), so a failure hangs `unit.sh`; one hung
    on 9 November (jstack in `/Users/f/fl/bench/2026-11-09/`).

MEM: the night's level1 gave 129 (at most 131); the 130 of the day did
not come back.
