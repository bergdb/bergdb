# 013-01 The unattended night

Created 2026-10-28 by Claude (Opus 5.5, Claude Code), at Frans's request.
Status: open.

This describes how an AI session works on BergDB without Frans, from about
noon until 07:00 the next morning. It is written for Frans, for Claude, and
for any other AI agent asked to run such a night. It comes from the first
night, 27 to 28 October 2026 ([006-09](../006-2026-q4/09-unattended-27-28-october.md)),
which Frans found worked well ("This way of working seems really good!").

Claude Code's tool names are given in parentheses. Another agent uses
whatever does the same job.


## 1. The idea in brief

* **Before Frans leaves**, the session writes a plan and asks him the few
  questions that would otherwise stop the work.
* **During the day**, subagents develop in scratch clones. The session
  checks their results, runs the gates and commits in Frans's name.
* **In the evening**, timed measurements are prepared as scripts and
  smoke-tested. CPU-heavy work stops.
* **At night**, a shell script outside the AI session (the *conductor*)
  runs the measurements on a quiet machine, around the nightly `night.sh`.
* **In the morning**, the session writes the results into the items, gives
  the plan an Outcome with a numbered list of decisions for Frans, and
  writes one summary entry in `news.md` by 07:00.

Two things make it work:

* everything is written down as it happens, so that any agent can pick it
  up;
* nothing depends on the AI session staying alive. A usage limit can stop
  it for hours.


## 2. Roles

| Who | Does |
|---|---|
| Frans | Asks for the night, answers the plan's questions before he leaves, decides in the morning. His own sessions may work in parallel. |
| The lead session | Plans, briefs and checks the subagents, runs the gates, commits, writes the plan's progress, the Outcome and `news.md`. The only one that commits. |
| Subagents (Agent) | One task each, in a scratch clone of their own, from a brief that points to an item; they write their state into that item as they go and report back. They do not commit to `main`. |
| The conductor | A shell script started with `nohup` outside the session. It runs the timed steps at night and writes a fallback news entry if the session is gone. |
| `night.sh` | The nightly test run, from launchd at 02:10. Left alone. |
| Other sessions | Frans's sessions on other items. Their uncommitted edits are preserved; they are asked before their code is touched. |


## 3. Before Frans leaves: the plan

1. **Read the current state:**
   * `items/readme.md`;
   * the Open tables of `items/015-todo/readme.md` and
     `items/005-todo/readme.md`;
   * the principles, `items/010-principles/01-principles.md`;
   * `news.md`, `git log`, `git status`;
   * which other sessions are working and on what. In Claude Code,
     `~/.claude/sessions/*.json` shows each session's name and whether it
     is busy.
2. **Choose the work.** A task fits the night when:
   * its "Done when" is clear and can be checked by gates or measurements;
   * no decision of Frans's is needed halfway.

   Leave out decisions (Kind: decide), items another session owns, and
   anything that cannot be gated. Order the tasks by value. Add a list of
   tasks to take "if there is time".
3. **Write the plan** as a subitem of the quarter's item (006-09 was
   one). Sections:
   1. the request, quoted, and Frans's answers;
   2. the ground rules;
   3. the work, W1 to Wn;
   4. the principles each task must keep;
   5. the timeline;
   6. what happens if the session stops;
   7. progress, a log with times;
   8. the Outcome.
4. **Ask Frans the blocking questions,** and quote his answers in
   section 1. Typical questions:
   * may the session commit to `main`;
   * may it put a given change into `java/`;
   * who decides when an item is done;
   * may `night.sh` move or be skipped;
   * how much usage, and at which effort.
5. **Set up the safety net** of section 6 before he leaves.


## 4. Ground rules

* **Clones.**
  * Code and Lean work is done in scratch clones, such as
    `/Users/f/fl/bench/<plan-id>/<task>/`.
  * The main tree only takes finished, gated changes, by cherry-pick or
    copy. Check first that `java/` and `lean/` in `main` have not changed
    since the clone's base. If they have, rebase and gate again.
* **Gates.**
  * A change to `java/` needs `java/before-commit.sh` (`BEFORE COMMIT OK`)
    and the level script of the mechanism it changes (`level2.sh` to
    `level4.sh`).
  * A change to `lean/` needs a clean `lake build`, with no `sorry` and no
    new axiom.
  * Gate the combined tree, with the night's earlier changes in it.
* **Commits.**
  * In Frans's name, with no AI attribution, by the lead session only.
  * Commit only this work's files or hunks, never another session's
    uncommitted edits. The Git index is shared by all sessions, so stage
    only right before committing, then commit at once.
* **Timing.**
  * Timed runs only in the quiet block (section 7).
  * Byte counts, memory and other deterministic measurements may run at
    any time.
  * Check s1 with `ps` before each run there; other sessions time there
    too.
* **Subagents.**
  * At most the number Frans allows (4 in 006-09).
  * Set the effort on every call: xhigh, or high when usage is tight
    (013-02, section 9). Another level only when Frans asks for it; never
    medium.
  * Each brief names the item, the clone, the files in the main tree the
    agent may write (only its own item's), the hard stop time, and the
    length of its report.
* **Principles.**
  * Every task is checked against 010-01.
  * A departure is written there, under its principle.
  * No new setting (P10), no global state (P9), no new timer or polling
    thread (P3), simple first (P11).
* **News.** `tools/news.sh STATUS SOURCE TEXT` when something finishes,
  fails or needs Frans; STATUS is `OK`, `FAILED` or `needs a look`. One or
  two lines and a reference; the details belong in the item.
* **Times.** Take the times written in logs from `date`, never from
  expectations. 006-09 had to correct several entries.
* **Raw output.** Test runs' raw output does not go into the repository
  (Frans, 2026-10-28). Keep the scripts, the summary tables and the
  findings in the item.


## 5. The day: development

* **Start the subagents** on W1, W2 and so on, each in its own clone, with
  a brief written as for a peer who knows nothing of the conversation:
  * the goal and the item;
  * what is already known or ruled out;
  * the rules of section 4.

  The item, not the conversation, holds the task.
* **State in the item.** A subagent keeps a short "State" note in its item
  (what is done, the clone, the next step). A fresh agent can then
  continue from it after a usage limit or a crash.
* **Check, then commit.** The lead session reads each report and checks
  the claims that matter: the gate output, the diff, the numbers. It
  copies the work into `main`, gates the combined tree and commits. A
  failure found on the way is fixed, or registered as a new 015 entry for
  Frans.
* **Prepare the night's steps.** Every timed run is a script in its item's
  directory (`night/…sh`), as described in section 7.
* **Progress.** Each finished piece gets a line in the plan's progress
  section, with the time and the commits, and a `news.md` entry if Frans
  should see it.
* **Pace the usage.** With a 5-hour usage window, prefer fewer agents in
  parallel when the window runs low. If Frans says it has reset, resume.
* **About 21:45: CPU-heavy work stops.** No builds, gates or Lean after
  that. A subagent still working writes its state and stops. The session
  checks that the conductor is alive and its steps are ready, writes the
  state into the progress section, and goes idle.


## 6. Surviving a usage limit or a dead session

The AI session can stop for hours (a usage limit, the machine sleeping, a
crash). Three things carry the work over:

1. **The conductor** runs the night's timed steps whether the session is
   alive or not (section 7).
   * Started at noon with `nohup caffeinate -i sh conductor.sh &`.
   * At the end of the quiet block it writes one `news.md` entry.
   * At 06:50 it checks for a marker file, `summary-written`. If the
     marker is missing, it writes a short summary entry itself, so that
     Frans gets news in any case.
2. **Check-ins**: prompts that the session schedules for itself
   (CronCreate), which fire while the session is open:
   * every hour during the day (12:17 to 21:17): find what was
     interrupted and resume it. A subagent that stopped without a report
     is resumed with a message (SendMessage). A finished output is read,
     and the timeline goes on. If all is on track, the check-in ends in
     one line.
   * 21:41: prepare the quiet block and go idle.
   * 05:57: the morning's work (section 8).
   * 06:27 and 06:44: second and last chances. Each does less than the
     one before; the last only writes the summary and touches the marker.

   The prompts used in 006-09 are in section 10.
3. **State on disk.** A scratchpad `state.md` holds the agent IDs, the
   clones and the events. The plan's progress section and the items' State
   notes hold the rest.

In 006-09 a usage limit stopped both running agents from 14:45 to 15:20.
They failed with HTTP 429 and were resumed after the reset. To find a
subagent's last activity, `stat -L` its output file; it is a symlink, so a
plain `stat` gives the link's time.


## 7. The night: the quiet block

Timing on F53 is disturbed by any other activity, including the AI session
itself and Frans's other sessions. So timed runs happen at night, one at a
time, on a quiet machine.

**Windows.** `night.sh` runs at 02:10 from launchd and takes about 40 to
60 minutes; it is not moved. So the block has two windows:

* window 1, 22:30 to 02:05;
* window 2, from `night.sh`'s end to 06:15.

The time before 07:00 is left for the write-up.

**`steps.txt`.** One line per step: `MINUTES|WHERE|SCRIPT|LABEL`, where
WHERE is `f53` or `s1`. The conductor reads the file again before each
step. To change it, write a new file and `mv` it over the old one.

**Markers.**
* A step runs only if `SCRIPT.READY` exists. Whoever prepared the script
  writes this marker, after a smoke test (`SMOKE=1`, about a minute).
* The conductor writes `SCRIPT.DONE` after the step, so a step runs once.
* Remove both markers in the morning.

**Step scripts.**
* A line `# minutes: N` gives the step's length. The conductor starts a
  step only if it ends inside the window.
* A script uses only what was built in the day: preserved builds in a
  clone, compiled probes. It compiles nothing.
* It checks its own needs (for example, s1 free) and exits with a
  non-zero code if the run did not happen.
* Its output goes to the item's `night/out/` or to the conductor's
  `out/LABEL.txt`.

**The quiet check.** The conductor runs 6 checks 30 s apart, all of which
must pass:
* no JVM except the editor's;
* no build, gate, Lean or `night.sh`;
* no busy Claude session;
* a 1-minute load below 2.

After 30 minutes without passing, the step runs anyway and is marked `NOT
QUIET` in `results.txt`. In 006-09 Frans's sessions in the evening made one
step run not quiet.

**s1 steps** run one after another in the background from window 1's
start. They check s1 themselves.

**The session is idle** for the whole block: no tool calls, no builds, no
agents.

**Outputs.**
* `results.txt`: one line per step, with its exit code and minutes.
* `conductor.log`.
* `status.txt`: one line, the current state.
* `out/LABEL.txt`: each step's output.
* At the end, one `news.md` entry: `OK` if every step exited 0, otherwise
  `FAILED` or `needs a look`.

[01-night/conductor.sh](01-night/conductor.sh) is 006-09's conductor.
[01-night/steps-example.txt](01-night/steps-example.txt) is its steps file.
For a new night, copy both to a new directory under `/Users/f/fl/bench/`
and set the times: `W1_START`, `W1_END`, `NIGHT_LATEST`, `W2_END` and
`FALLBACK`, in the script or the environment. Also set `BASE`, and the
item named in its news text.


## 8. The morning

From 05:57, after the block has ended (the conductor's `status.txt`):

1. **Results into the items.** Each step's results are written into its
   item: what was measured, the numbers, what they mean. Summaries and
   tables are kept; raw output is not committed.
2. **Status.** Items that Frans allowed the session to close are closed.
   Changes he allowed are committed if their conditions held.
3. **The plan's Outcome** (section 8 of the plan):
   * **Done, in `main`**, with the commits.
   * **The night**: what ran, what failed and why.
   * **For Frans to decide**: a numbered list. Each item has the question,
     where to read about it, and a recommendation.
   * **Left**: what waits for the next quiet block.
4. **The summary in `news.md`** by 07:00, with `tools/news.sh "needs a
   look"` if there are decisions. It gives two or three lines: what was
   done, what the night showed, and the decisions with the plan's ID. Then
   touch `summary-written`.
5. **Clean up.**
   * Remove the step markers.
   * Leave the conductor to end by itself: it ends after 06:50.
   * Delete the recurring check-in.
   * Leave other processes alone; Frans often has things running.

**When Frans returns** he works through `news.md`, often in his own
sessions, one decision each. When he asks, the lead session updates the
Outcome's list to the current state:
* which decisions he made;
* which are under way and in which session;
* what is left, each item with a recommendation.

It also updates the summary entry in `news.md`. Then the session can be
closed.


## 9. Lessons from 006-09

* **`performance.sh` has its own quiet check** (90 percent idle CPU). It
  refused 005-48's F53 runs at 00:57, although the conductor had just
  found the machine quiet. Inside a conductor step, either pass `FORCE=1`
  (the conductor has already checked) or use the same check in both
  places.
* **A smoke test must check the output, not only the exit code.** Props
  exited 1 at night because its CORE output was not parsed. A smoke test
  that parses the result would have found it in the day.
* **Busy sessions of Frans's** count as not quiet, rightly. Plan the
  block's length with some slack.
* **Write a decision entry** (Kind: decide, in 015) when the night finds an
  API question. In 006-09, `BryanRepro` showed one: a start right after
  `stop()`. The test was fixed at once and 005-63 registered for Frans,
  instead of the session deciding by itself.
* **A subagent's Write may be refused** for a file. It then returns the
  text in its report, and the lead session saves it.
* **The Git index is shared.** In the morning a deletion this session had
  staged could have gone into another session's commit. Stage right before
  committing, and commit with a path list.
* **Times from `date`.** Several progress lines were written with expected
  times and had to be corrected.


## 10. The check-in prompts of 006-09

The prompts the session scheduled for itself on 2026-10-27, with paths and
IDs left out. They show how much each one does.

* **Hourly, 12:17 to 21:17:** "Read state.md and the plan's progress
  section. Check cheaply whether anything was interrupted: a subagent that
  stopped without its report (`stat` its output file for its last
  activity; never read that file), a background gate or script that ended
  unnoticed, a step of the timeline that is overdue. If so, resume it:
  SendMessage to the stopped subagent, read finished outputs, carry on
  with the timeline (commit gated work, update the progress, start the
  next subagent within the limit, news.md on a failure). If all is on
  track, end the turn with one line and no more tool calls."
* **21:41:** "Prepare the quiet block. Make sure every subagent has
  stopped CPU-heavy work (tell any that has not to stop at once and
  report), that no build, gate or Lean of this session runs, that the
  conductor is alive and its steps.txt lists the READY steps with their
  minutes, and that the s1 steps are in it. Record the state in the
  progress section. Then go idle: no tool calls during the block."
* **05:57:** "Read state.md and the conductor's status.txt. If the block
  still runs, start a background command that waits for the conductor's
  pid to end, and end the turn; continue when notified. Once the block is
  done: put the night's results into the items, decide statuses as Frans
  allowed, commit the gated work in Frans's name with no AI attribution,
  fill the Outcome, write the summary with tools/news.sh by 07:00, then
  touch summary-written."
* **06:27:** "If summary-written does not exist, the 05:57 check-in did not
  finish: do the most important parts now, in this order, all by 06:55:
  the summary entry in news.md, the Outcome, then commits of finished,
  gated work. Touch the marker after the news entry. If the marker exists,
  end the turn with one line."
* **06:44:** "If summary-written does not exist, write the summary entry
  in news.md now, from the progress section and the conductor's log, then
  touch the marker. Nothing else. If the marker exists, end the turn with
  one line."
* **After a usage limit** (one-off, at the expected reset): "Resume the
  paused subagents, or start new ones at the effort Frans wants from their
  items' State notes; keep within the limit of agents and pace usage; note
  in the progress that the work resumed."
