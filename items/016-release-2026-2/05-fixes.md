016-05. Plan: the fixes before the release, and their reviews
============================================================

Created 2026-11-03 by Frans Lundberg.

**Status: planned, not started.** The plan of W4 and H5 (016-01, sections
4.1, 5 W4, 6 H5 and 8): the entries to fix or settle before release
2026.2, who makes each, in which clone, with which gate, how each change
is reviewed, and how it reaches `main`. Each entry holds its own detailed
plan, in a section "Plan for 2026.2"; this plan holds the order, the
agents, the reviews, the hand-off and the quiet block.


## 1. What changed since 016-01

Three messages from Frans on 2026-11-03 set the frame (016-01, section 10;
016-02, section 1):

* 15:27, on 016-01's questions: "Q1: as recommended." (005-82: the live
  read only), "Q3. Use xhigh, no higher." and "Q4. Fix before. You decide
  how to." (015-01, the empty directory, is fixed before the release; the
  coordinator chooses its design).
* 15:31, D7: "The C code does not need to be updated for 2026.2 in this
  work. Only Java code will be included in the release. It is not a
  requirement to update the Lean code either. If this is needed to develop
  Java or to ensure it works well, then do it. See it as a tool, not an
  output artifact for the release."
* 15:40: "try your best to finish this work by 07:00 tomorrow in the
  morning ... instead of in three days or so. Note, you only need
  before-commit.sh to be successful to commit your work."

So, for this plan:

* **Java only.** No entry's C step is done for 2026.2 (005-69's C port of
  `SystemClock` becomes a later follow-up, written in its entry). Lean is
  touched only where it helps to check a Java change; none of the entries
  below needs it.
* **The gate is `java/before-commit.sh`** (`BEFORE COMMIT OK`), in the
  agent's clone and again on the combined tree. A level script runs only
  where this plan says "if it fits": when the machine has room and the
  change is in that level's mechanism. A level script that fails is a
  finding, and the change waits for it.
* **Tonight.** The fixes start at about 16:50. Everything is committed by
  about 01:30. The quiet block is in window 2 only, from the end of
  `night.sh` (about 03:00) to 06:05 (section 6). The release itself is
  016-09's; the probe of 005-52 is committed before its release commit.


## 2. The entries, in order

The order of 016-01, section 4.1. "Hours" are agent-hours, the working
time, the review's included; "entry": in that entry's plan.

| Entry  | Kind        | What, for 2026.2                                       | Agent | Hours |
|---|---|---|---|---|
| 005-82 | Fix         | `getTrans` fails the database on a corrupt record      | F1    | 1.5   |
| 005-79 | Implement   | integers in the Core's decisions, Java only            | F3    | entry |
| 005-78 | Investigate | the retain duration in the stream                      | F4    | entry |
| 005-69 | Fix, A      | `SystemClock` keeps its promise                        | F1    | 0.75  |
| 005-71 | Fix, A      | notes in 010-01's P2 and 012-05; no code               | F1    | 0.4   |
| 005-80 | Decide, B   | a line in 005-52's Outcome, a test of the race         | F1    | 1.5   |
| 005-52 | Fix         | `PauseProbe`'s `lower` and `lowerAt`; six runs         | F2    | 3     |
| 005-65 | Investigate | the rerun of `threads.sh` with the fix                 | F2    | 1.7   |
| 015-01 | Fix         | a directory without its stream is refused              | F5    | 4     |

The plans, each in its entry's section "Plan for 2026.2" (015-01's in its
"Recommendation"):

* [005-82](../005-todo/82-gettrans-corruption.md)
* [005-79](../005-todo/79-integers-not-doubles.md)
* [005-78](../005-todo/78-retain-duration-in-stream.md)
* [005-69](../005-todo/69-system-clock-promise.md)
* [005-71](../005-todo/71-dbclock-read-time-after-start.md)
* [005-80](../005-todo/80-setbudget-race-record.md)
* [005-52](../005-todo/52-cache-size-while-running.md)
* [005-65](../005-todo/65-gets-with-8-readers.md)
* [015-01](../015-todo/01-empty-directory.md)

005-79 and 005-78 are planned in their entries by another agent (016-02,
section 3); this plan links them and gives them the same review and
hand-off. 005-78 is a stop for Frans (section 8).

### 2.1. Agent-hours by step

From the entries' plans; the gates' wall time in brackets (F53, about 2
minutes for `before-commit.sh` when nothing else runs).

* **005-82** (F1), 1.5: the clone 0.05; the fix 0.25; the Javadoc 0.1;
  the tests and the mutation 0.35; `before-commit.sh` (2 min), and
  `level1.sh quick` if it fits (75 s); the review 0.5 (another agent);
  the answers 0.15; the hand-off 0.1.
* **005-69** (F1), 0.75: the clone and the fix 0.2; the two tests 0.2;
  `before-commit.sh` (2 min); its share of the review with 005-71, 0.15;
  the answers and the hand-off 0.2.
* **005-71** (F1), 0.4: the note in P2, with the check of the invariance
  tools, 0.1; the note in 012-05 0.05; no gate; its share of the review
  0.15; the hand-off 0.1.
* **005-80** (F1), 1.5: the hook 0.2; the test 0.4; the mutation check
  0.2; the line in 005-52 0.05; `before-commit.sh` (2 min), and
  `level4.sh quick` if it fits (4 min); the review 0.5; the answers and
  the hand-off 0.15.
* **005-52** (F2), 3: the probe's properties 0.75; its smoke 0.1;
  `before-commit.sh` (2 min); the review 0.5; the hand-off 0.1; the step
  script and its parser 0.2 (written with this plan; read and adjusted to
  the probe as made); the prep from the commit 0.2; the smoke and READY
  0.1; the block (25 min of the conductor's time); the table, the
  comparison and the close, in the morning, 1.
* **005-65** (F2), 1.7: the smoke and READY 0.3 (the wrapper is
  written); the block (30 min); the results, the explanation and the
  close, in the morning, 1.2; the review of the numbers 0.2.
* **015-01** (F5), 4: the order of the creation 0.4; A+ 0.3; the check
  and the exception 0.5; the Javadoc 0.3; the six tests 1.2;
  `before-commit.sh` (2 min), `level1.sh quick` and `level2.sh quick` if
  they fit (4 min); the review 0.75; the answers 0.4; the hand-off 0.1.
* **005-79** and **005-78**: in their entries (005-79's steps 1 to 5,
  four to five hours; 005-78's study and design tonight).

In all, without 005-79 and 005-78: about 12.9 agent-hours, of which 2.2
are in the morning (005-52's and 005-65's write-ups). Before 01:30: F1
about 4.2, F2 about 2.3, F5 about 4, the reviews' share included.

### 2.2. Clone, gate, review and hand-off, entry by entry

The clones are `/Users/f/fl/bench/016/ENTRY/repo` (section 3); the gate
is `java/before-commit.sh` everywhere `java/` changes; the review and the
hand-off are sections 5 and 4.

* **005-82**: F1. Gate: `before-commit.sh`; `level1.sh quick` if it fits.
  Review: the fix and the two tests against docs/levels.md, section 3,
  and 005-34; whether a parser exception other than a
  `StreamFormatException` can still escape. Hand-off: `java/` and the
  entry.
* **005-79**: F3. Its entry's plan (by another agent): its clone is
  `/Users/f/fl/bench/016/005-79`, its steps 1 to 5 about four to five
  agent-hours from about 16:50; this plan's review and hand-off;
  StreamDigest's new reference (016-01, section 3).
* **005-78**: F4. Its entry's plan: the clone `/Users/f/fl/bench/016/005-78`,
  the study and the design tonight, then a stop for Frans (section 8); the
  change (its U6) is about 1.5 days after his choice.
* **005-69**: F1. Gate: `before-commit.sh`; `level1.sh quick` if it fits.
  Review with 005-71's notes, by one agent. Hand-off: `java/` and the
  entry; the C port is not done (D7).
* **005-71**: F1. No gate (no `java/`). Review with 005-69. Hand-off: the
  notes in 010-01 and 012-05, and the entry.
* **005-80**: F1. Gate: `before-commit.sh`; `level4.sh quick` if it fits.
  Review: the interleaving written out, the hook, the mutation. Hand-off:
  `java/`, the entry, and the line in 005-52's Outcome (applied before or
  after F2's 005-52 patch, `git apply --3way`).
* **005-52**: F2. Gate for the probe: `before-commit.sh`. Review: the
  probe's change; the scripts are read by the same reviewer. Hand-off in
  two parts: the probe (`java/stress/PauseProbe.java`) and the entry by
  about 19:00; the table and the close after the block. The night
  scripts are in the main tree already (section 3).
* **005-65**: F2. No gate. Review: the morning's numbers against
  `summary.txt`. Hand-off: the entry, `night/results-2026-11-04.txt`;
  the wrapper is in the main tree.
* **015-01**: F5. Gate: `before-commit.sh`; `level1.sh quick` and
  `level2.sh quick` if they fit. Review: the order of the creation, the
  check before the open, the six tests, the Javadoc, the new exception
  (the only Pub API addition of W4). Hand-off: `java/`, the entry, and
  015's table row (the coordinator).


## 3. The agents and the clones

* **The slots.** At most 4 subagents at a time (016-02, section 2), shared
  with the documents (016-03, 016-04), 005-79 and 005-78, and the reviews.
  W4's small entries need two slots from 16:50 (F1 and F2), and a third
  for 015-01 (F5) once one is free. Each review (section 5) takes a slot
  for 0.3 to 0.75 hours.
* **One clone per entry**, made by the agent from `main`:
  `git clone -q /Users/f/fl/repos/bergdb /Users/f/fl/bench/016/ENTRY/repo`
  (ENTRY as `005-82`), then `git -C .../repo rev-parse HEAD > .../BASE`.
  An agent that takes several entries in a row makes a new clone for
  each, from `main` as it is then, so that each hand-off has its own base.
* **What an agent writes** in the main tree: nothing but its entries'
  night scripts (005-52 and 005-65, section 6) and their READY markers.
  Code, tests and the entries' Log and Outcome are made in the clone and
  handed off (section 4).
* **The briefs** (013-01, section 4): the item and entry, the clone, the
  files it may write, the hard stop time, the report's length, xhigh
  effort (Q3). Each brief adds these rules:
  * Java has trailing whitespace: edit with exact strings (a Python
    replace), not a tool that strips it, and check `git diff -w` against
    `git diff`.
  * Every test stops or closes its databases (`DbTester`'s check, the
    leak check).
  * No timed run outside the quiet block; byte counts and smoke runs are
    fine.
  * `before-commit.sh` one at a time on F53: before starting it, check
    with `ps` that no other `before-commit.sh` or level script runs; wait
    if one does.
  * A fault found outside the entry goes to the coordinator as a finding
    (016-01, section 6, the rule for findings); the agent does not fix it.


## 4. The hand-off

What, by whom, and how it is checked:

1. **The agent, for the review**: when the change, its tests and the
   gate are done in its clone, it writes
   `/Users/f/fl/bench/016/ENTRY/handoff/`:
   * `BASE`, the clone's base commit;
   * `files.txt`, the paths changed, one a line;
   * `patch.diff`, `git -C repo diff BASE` with new files included
     (`git add -N` first);
   * `gates.txt`, the gates' last lines with their times from `date`.

   It tells the coordinator (a message, or its report if its run ends
   there), and goes on with its next entry. The coordinator starts the
   reviewer (section 5); subagents do not start agents.
2. **The agent, after the review**: the coordinator passes the findings
   on (SendMessage to the author, or a new agent with the clone if the
   author has ended). The author answers each in the entry's Log, fixes
   the faults, runs `before-commit.sh` again if `java/` changed, writes
   the entry's Log (what was done, the gates, the mutation, the findings
   and their answers) and, where it closes, its Outcome and Status line,
   and writes `patch.diff`, `files.txt` and `gates.txt` again, with
   `review.txt` (the findings and the answers). Then it reports in about
   15 lines.
3. **The coordinator** checks that `main`'s `java/` and `lean/` are still
   the base's: `git -C /Users/f/fl/repos/bergdb diff --quiet BASE HEAD --
   java/ lean/`. If not, the agent (or the coordinator) rebases the clone
   on `main` and runs `before-commit.sh` again.
4. **The combined gate**: in a clone of `main` with the patch applied
   (`/Users/f/fl/bench/016/combined/`, `git apply --check`, then `git
   apply`), `java/before-commit.sh` must print `BEFORE COMMIT OK`. Several
   hand-offs that arrive together are gated together. A patch that does
   not touch `java/` (005-71's notes, 005-65's write-up) needs no gate.
5. **Into `main`**: `git apply` of the same patch in the main tree, then
   `git diff --stat` compared with `files.txt`; the other sessions' edits
   stay (AGENTS.md).
6. **The commit**: staged right before it, with the path list of
   `files.txt`; in Frans's name, with no AI attribution; the message
   names the entry, the decision, the tests and the gates (as `988fe1a`'s
   does). Before it, `main`'s `java/` and `lean/` are checked once more
   against the gated tree (Frans may commit meanwhile).
7. **The bookkeeping**: the entry's row in 005's or 015's table (the
   coordinator sets the status), a line in 016-02, `releases/next.md`
   through 016-03's agent, and `tools/news.sh` for what finishes or
   fails.


## 5. The reviews (H5)

Every change of W4 is reviewed before the hand-off, by an agent that did
not write it, at xhigh (Q3).

* **What the reviewer gets**: the entry (its issue, options, decision and
  "Plan for 2026.2", not the author's Log); the diff (`patch.diff`); the
  tests; a copy of the author's clone of its own
  (`/Users/f/fl/bench/016/ENTRY/review/`, `cp -R` of `repo`), where it may
  build and run single test classes, not the gates; and the documents the
  entry cites (docs/levels.md, section 3, for 005-82; 010-01's principles
  for every entry).
* **What it is asked**:
  * Is the change correct against the entry's "Done when" and the
    contracts it cites?
  * Does each new test fail without the change, and pass with it? (The
    author records the mutation it used; the reviewer may try another.)
  * Is a Javadoc or comment now wrong?
  * Does the change touch a stream byte (it must not, except 005-79's
    take), a Pub API signature (only 015-01's new exception), or a
    principle of 010-01?
  * For 005-80: the interleaving, written out, and the test's hook.
* **What it returns**: a list of findings, each "fault", "doubt" or
  "nit", with its evidence (a failing test, or the file, the line and the
  reasoning), at most 40 lines, to the coordinator, which passes it on.
* **How findings are answered**: the author answers each in the entry's
  Log ("fixed, with test T", or "not a fault, because ..."). A fault is
  fixed and gated again. The same reviewer reads the answers again only
  when the fix is more than about 20 lines (SendMessage to it). A
  disagreement goes to the coordinator; a design question in it is a stop
  for Frans. A finding outside the change is registered by the coordinator
  in 015 (016-01, section 6).
* **Time**: 0.3 hours for 005-69 and 005-71 together, 0.5 for 005-82,
  005-80 and 005-52's probe, 0.75 for 015-01.


## 6. The quiet block, night 1

Window 2 only, from `night.sh`'s end (about 03:00) to 06:05, by the
conductor in `/Users/f/fl/bench/016/night1/` (013-01, section 7), in this
order. That conductor runs since 15:42 (`conductor.log`), with window 1
empty (02:00 to 02:00), `NIGHT_LATEST` 03:15 and `W2_END` 06:05; its
`steps.txt` has no step yet.

| Step | Script | Minutes | Ready by |
|---|---|---|---|
| 65-rerun | `items/005-todo/65-gets-with-8-readers/night/rerun-016.sh` | 30 (about 21) | 18:00 |
| 52-lowered | `items/005-todo/52-cache-size-while-running/night/lowered.sh` | 25 (about 17) | 01:30 |

Their `steps.txt` lines (the conductor's agent or the coordinator writes
the file):

    30|f53|/Users/f/fl/repos/bergdb/items/005-todo/65-gets-with-8-readers/night/rerun-016.sh|65-rerun
    25|f53|/Users/f/fl/repos/bergdb/items/005-todo/52-cache-size-while-running/night/lowered.sh|52-lowered

The rules for both scripts (013-01, section 7):

* A line `# minutes: N` gives the step's length.
* The script uses only what was built in the day: 005-65's four builds in
  `/Users/f/fl/bench/006-10/e65-builds`, checked on 2026-11-03 (section
  9); 005-52's jar and probe classes in `/Users/f/fl/bench/016/005-52/run/`.
  It compiles nothing.
* It checks its needs (the java binary, the jars, the classes, the probe's
  new properties) and exits 2 if one is missing; 1 if a run failed or the
  parsed summary is incomplete; 0 otherwise.
* `SMOKE=1` runs it small (about a minute), with outputs outside the
  repository, and checks the parsed summary, not only the exit codes; it
  prints `... (SMOKE): OK`.
* The agent that prepared it writes `SCRIPT.READY` after the smoke test,
  and records the smoke's last line in the entry's Log. The conductor
  writes `SCRIPT.DONE`. Both markers are removed in the morning.
* Neither uses `performance.sh`, so neither needs `FORCE=1`; the
  conductor's quiet check comes first, and `threads.sh` checks quiet
  again (two checks 15 s apart).
* Raw outputs stay outside the repository; the summary tables go into the
  entries in the morning.

What each step needs is in its entry's "Plan for 2026.2".


## 7. The schedule

Times are planned; 016-02 records the real ones.

* 16:50 to 17:10: the coordinator chooses 015-01's design (015-01's
  recommendation: A with A+) and commits the plans.
* F1, from 17:00: 005-82 (to 18:30, the review in a free slot), 005-69
  (to 19:15), 005-80 (to 20:45), 005-71's notes (to 21:10). Each handed
  off when it is done.
* F2, from 17:00: 005-65's smoke and READY (to 17:20); 005-52's probe
  and its smoke (to 18:15), its review (to 19:00) and hand-off; the
  coordinator commits the probe (by about 19:30, in any case before the
  release commit); then the prep of `/Users/f/fl/bench/016/005-52/run/`
  from that commit, the scripts read against the probe, the smoke and
  READY (to 20:30; at the latest 01:30).
* F5, from about 17:15 (or when a slot is free): 015-01, steps 1 to 6, to
  about 21:15, its review to 22:00.
* F3 and F4: 005-79 and 005-78, by their entries.
* By 01:30: everything of W4 that is done is committed; the scripts are
  READY.
* 03:00 to about 04:00: the quiet block; the session and the agents are
  idle. From its end (the conductor's `status.txt`), 005-65's and
  005-52's write-ups: 2.2 agent-hours, two agents in parallel, done by
  about 05:30 if the block ends by 04:00; the entries close or stay open
  with their State.

**What cannot fit tonight:**

* **The slots.** Four slots from 16:50 to 01:30 give about 35
  slot-hours, shared with the documents (016-03, 016-04), the search
  (016-06 to 016-08) and 005-79 and 005-78. W4 needs about 11 of them
  before 01:30 (F1 4.2, F2 2.3, F5 4), plus 005-79's and 005-78's. If the
  search needs more, F1's and F5's entries come first: they change the
  release's code; 005-52's step script can be READY as late as 01:30.

* **005-78's change.** It waits for Frans's choice among its forms, each a
  question of the stream format (016-01, section 3), and is about 1.5
  days of work after it (its entry, U6). It does not fit tonight: its
  study and design are done, and the retain duration stays as it is, a
  known issue in the notes, unless Frans decides otherwise.
* **005-79**, if its Java part takes more than its entry's plan says: its
  entry has the cut-off. Its Lean and C steps are not done (D7).
* **005-52's and 005-65's write-ups** are in the morning, after the
  block; if the block is late or not quiet (`NOT QUIET` in
  `results.txt`), the entries stay open and say so; the release does not
  wait for them (they change no code of the release, except the probe).
* **015-01's case 3** (an empty or missing directory) is not fixed by its
  recommendation; it goes to Frans as a question for after the release.


## 8. Stops for Frans

Each gets `tools/news.sh "needs a look"` and a line in 016-02's "For Frans
to decide"; the other work goes on.

* 005-78's design (a stream format question).
* 015-01: only if the coordinator takes B1 (it changes how every program
  creates a database), or a design that makes the start read something new
  from the stream.
* 005-52: a wait in the lowered runs longer than with a fixed budget,
  beyond the spread of the two fixed runs: its cause and a proposal, before
  any change to `java/` (the entry's rule).
* 005-65: a result against the expectation of its State, step 3: the
  explanation and a recommendation; a change to `java/` is Frans's.
* A review's disagreement that is a design question.


## 9. State

2026-11-03, 15:55, by the planning agent:

* Written: this plan; "Plan for 2026.2" in 005-82, 005-69, 005-71, 005-80,
  005-52 and 005-65; the new 015-01 with its row in 015's table.
* Night scripts written, none smoke-tested, no READY marker: 005-65's
  wrapper `night/rerun-016.sh`; 005-52's `night/lowered.sh` and
  `night/sum52.py` (the parser tried on made-up outputs of the planned
  format). `PauseProbe` is unchanged, so 005-52's smoke waits for the
  probe's commit.
* The four builds in `/Users/f/fl/bench/006-10/e65-builds` exist, clean,
  with the jars that 005-65's State names (`308e7d01`, `79925f95`,
  `2b5202f0`, `517165ee`, the first 8 hex digits of their SHA-256), and
  `sb/` with each build's ScaleBench classes and `pidio`. The JDK at
  `/opt/homebrew/opt/openjdk` is 27 (`Cellar/openjdk/27`); Q2's JDK 17
  was installed beside it as `openjdk@17`
  (`/Users/f/fl/bench/016/brew-openjdk17.log`, exit 0), which changes
  nothing here. A Homebrew upgrade of `openjdk` before the block would
  change the JVM under both steps: none is to be made tonight.
* The conductor in `/Users/f/fl/bench/016/night1/` runs (since 15:42),
  waiting; its `steps.txt` is empty. The coordinator adds section 6's two
  lines (a new file, then `mv`).
* Nothing is started: no clone, no agent, no run.
* To resume: take section 7's schedule from where 016-02 says the work
  is, and each entry's "Plan for 2026.2" and State.


## Log

2026-11-03. Created, at the coordinator's request, from 016-01 with
Frans's answers of 15:27, D7 (15:31) and his message of 15:40: Java only,
`before-commit.sh` as the gate, everything committed by about 01:30, the
quiet block in window 2.
