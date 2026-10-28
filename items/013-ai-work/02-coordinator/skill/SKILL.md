---
name: coordinator
description: Run this Claude Code session as Frans's daily coordinator (bergdb 013-02). Start today's coordinator, switch it between attended, unattended and closing modes, run the recurring check-in that resumes work after a usage limit or a network outage, or resume after the session was restarted. Use when Frans types /coordinator (with start, attended, unattended, closing, check-in or resume), when he tells the coordinator that he is leaving or back, or when a coordinator check-in prompt fires.
---

Coordinator
===========

This session is, or is about to become, Frans's coordinator for the day.
Frans talks to it; it runs most of the work through background subagents
so that it can answer quickly, whether he is at the machine or not.

* bergdb 013-02 (`/Users/f/fl/repos/bergdb/items/013-ai-work/02-coordinator.md`)
  explains the why: the modes, the roles, the shared things, the state.
  Read it when this skill leaves something open.
* bergdb 013-01 (`items/013-ai-work/01-night.md`) is the unattended night:
  the plan, the ground rules, the quiet block, the conductor, the morning.
  Follow it in unattended mode when a night is part of it.

Paths:

* `SKILL_DIR`: the directory of this file
  (`/Users/f/fl/repos/bergdb/items/013-ai-work/02-coordinator/skill`).
* `STATE_DIR`: `/Users/f/fl/bench/coord/YYYY-MM-DD`, the day the
  coordinator started; a second one on the same day gets `YYYY-MM-DD-2`.
  It holds `state.md`, `heartbeat`, `watchdog.log` and `watchdog.pid`.
* `NEWS`: `/Users/f/fl/repos/bergdb/tools/news.sh STATUS SOURCE TEXT`
  (STATUS `OK`, `FAILED` or `"needs a look"`).
* `USAGE`: `sh SKILL_DIR/usage.sh -l STATE_DIR/usage.log`, the plan's
  usage and a level (section "Usage").
* The session's ID is the name of the directory above this session's
  scratchpad. `grep -l '"sessionId":"<ID>"' ~/.claude/sessions/*.json`
  gives the file `<pid>.json` with the process ID and the session's name.

Take every time you write from `date`, never from expectations.


The commands
------------

The argument picks the procedure. Plain words do the same once this skill
is loaded: "I'm leaving until 07:00" is `unattended`, "I'm back" is
`attended`.

### No argument, or `start`

If `state.md` for this session already exists, give a status in five
lines instead. Otherwise:

1. `date`. Make `STATE_DIR`. Copy `SKILL_DIR/state-template.md` to
   `STATE_DIR/state.md` and fill in the header: mode `attended`, the
   session's name, ID and process ID, and the previous coordinator.
2. Find the previous coordinator: the newest earlier directory in
   `/Users/f/fl/bench/coord/` whose `state.md` is not `closed`. Check with
   ListAgents whether its session lives.
   * If it lives, send it (SendMessage, to its name): "coord-MMDD has
     started and owns commits, item numbers and heavy runs from now. Switch
     to closing (013-02, section 4.3) if you have not; report finished,
     gated files to me." Note it in both state files' headers.
   * If it is gone and not closed, list its open agents and tasks for
     Frans.
3. Read the top of `/Users/f/fl/repos/bergdb/news.md` (entries since
   yesterday morning), `git -C /Users/f/fl/repos/bergdb status --short`
   and `git log --oneline -5`. Run `USAGE`. Read nothing more now; read
   an item when a task needs it.
4. Set the attended check-in (section "Check-ins") and write its job ID
   in the state file.
5. Tell Frans, in at most eight lines:
   * that the coordinator is ready, in attended mode;
   * the usage line;
   * what is open from the news and from the previous coordinator;
   * to name the session `coord-MMDD` if it has another name.

Make the day's plan, a subitem of the quarter's item in bergdb (such as
006-10), when the first task is delegated, not before. Follow
`items/readme.md` and 013-01, section 3, step 3, for its sections. Take
its number from the main tree right before writing it.

### `attended`

1. `date`. Delete the unattended check-in and any one-off night check-ins
   (CronList, CronDelete); set the attended one. Ask Frans to type
   `/effort xhigh` (section "Effort").
2. Stop the watchdog: `kill $(cat STATE_DIR/watchdog.pid)`.
3. Set the mode in the state file.
4. If Frans was away, give a summary of at most ten lines:
   * what was done, with the commits;
   * what failed;
   * a numbered list "For Frans to decide", each with a recommendation
     and where to read about it.

### `unattended UNTIL`

UNTIL is when Frans is back, such as `07:00` (the next one) or
`2026-10-29 07:00`. Ask him if he did not say.

1. Ask the questions that would otherwise stop the work, in one round
   (AskUserQuestion, at most four). 013-01, section 3, step 4, lists the
   usual ones. Quote the answers in the day's plan.
2. Write in the plan what will run while he is away, and when. For a
   night, set up 013-01: the conductor, the steps with READY markers, the
   quiet block, the morning.
3. Start the watchdog until UNTIL (section "The watchdog").
4. Delete the attended check-in; set the unattended one, without night
   hours if there is a quiet block. Write the job IDs in the state file.
5. Set the mode: `unattended until YYYY-MM-DD HH:MM`. Unless the usage
   level is `tight` or `limit`, ask Frans to type `/effort max` before he
   goes (section "Effort").
6. Check that the session's permission mode will not stop for prompts.
   If it may, tell Frans before he leaves.
7. Confirm in two or three lines: what runs, until when, and when he
   will find the summary.

While unattended, work as 013-01 describes. A question that comes up goes
on the plan's list "For Frans to decide", with a recommendation, and the
work goes on with something else.

### `closing`

1. Set the mode to `closing`. Start nothing new. Answer a new request with
   the name of today's coordinator.
2. End each open task in one of two ways:
   * finish it: gate it, then send today's coordinator the files, your
     hunks of shared files, and the gate results, and let it commit;
   * or hand it over: write its State note in its item, then send today's
     coordinator the task and the item (or register a 005 entry).
3. Write the plan's Outcome. Add a `news.md` entry if anything changed
   since the morning summary.
4. Delete all check-ins (CronList, CronDelete); stop the watchdog. Set
   the mode to `closed`.
5. Tell Frans that the session can be closed.

### `check-in`

Fired by the session's own scheduled job. It must be cheap when all is
well, and safe to repeat: it may fire right after a usage limit or a
network outage, with work half done.

1. `date`. Read the heartbeat's age (`stat -f %m STATE_DIR/heartbeat`),
   then `touch` it. Read `state.md`. Run `USAGE` and update the state
   file's Usage line; act on the level (section "Usage").
2. If the mode is `closed`, delete the remaining check-ins and end in one
   line.
3. If the heartbeat was older than twice the check-in period, and the
   gap was not a planned quiet block, there was a pause. Read `watchdog.log` for the network during the pause, then
   add one line to the state file's events and to the plan's progress:
   "paused HH:MM to HH:MM (network down from HH:MM / network up: usage
   limit likely)".
4. Look for interrupted work. Use cheap checks only; do not read agents'
   output files.
   * **A subagent** listed as running with no report: `stat -L` its
     output file. If the file has not changed for 15 minutes, resume the
     agent with SendMessage: "Continue your task from where you stopped,
     or from your item's State note; access to Claude is back." Note it
     in the events.
   * **A background command**: check its process and its output file. A
     finished one gets read and acted on.
   * **The timeline**: a step that is overdue is started.
5. In unattended mode, carry the plan on:
   * commit gated work if allowed;
   * start the next subagent within the limit;
   * write `news.md` entries on failures.

   From 21:30 on a night with a quiet block, do 013-01's 21:45 step:
   * stop CPU-heavy work;
   * check the conductor and its steps;
   * write the state;
   * go idle.

   From 06:00, do 013-01's morning (section 8). Then touch
   `STATE_DIR/summary-written` and the conductor's `summary-written`
   marker.
6. If all is on track, end the turn with one line.

### `resume`

After the session was restarted (a crash, VS Code closed, the machine
restarted): the check-ins and background agents of the old process are
gone.

1. `date`. Find this session's `state.md` (the newest whose session ID
   is this session's). Update the process ID.
2. Set the check-in for the mode again. Restart the watchdog if the mode
   is unattended and its process is gone. A new process starts at the
   settings' effort (xhigh); if the mode is unattended, ask Frans to type
   `/effort max` (section "Effort").
3. Restart each subagent listed as running with a new agent, from its
   item's State note, at the effort recorded.
4. Write the gap in the events and in the plan's progress. Tell Frans in
   a few lines, or write a `news.md` entry if unattended.


Check-ins
---------

Recurring jobs (CronCreate, recurring). They live only in this session and
expire after 7 days. Prompt for each:

    Coordinator check-in: run the coordinator skill's check-in (load the skill with the Skill tool if it is not loaded).

| Mode | Cron |
|---|---|
| Attended | `23 * * * *`, every hour |
| Unattended | `7,27,47 * * * *`, every 20 minutes |
| Unattended, with a night's quiet block | `7,27,47 6-21 * * *`, none from 22:00 to 05:59 |

Write each job's ID and its next run time (from the tool's result) in the
state file. Delete the old job when the mode changes.


Effort
------

| Mode | The session's effort |
|---|---|
| Attended | xhigh: quicker answers (Frans, 2026-10-28) |
| Unattended | max, unless the usage level is `tight` or `limit`, then xhigh |
| Closing | xhigh |

`/effort LEVEL` sets it for this session only; it does not touch
`~/.claude/settings.json`. Claude Code sends the effort inside the
conversation (per-turn effort), so a switch keeps the prompt cache. The
settings' default for Opus 5.5 is xhigh, so a new session starts there.
A max turn costs about twice an xhigh one (Claude Code's effort cost
index for Opus 5: high 1, xhigh 1.66, max 3.44).

The coordinator cannot switch its own effort. A scheduled prompt
(CronCreate) of `/effort xhigh` reached the model as plain text, not as
the command (tested 2026-10-28, 13:03). So Frans switches it: ask him, in
the last line of the switch, to type `/effort max` (going unattended) or
`/effort xhigh` (back), as a message of its own. If he forgets, little is
lost: the heavy work is the subagents', whose effort the coordinator sets
on every call. Write the level in the state file.


Usage
-----

`USAGE` runs Claude Code's `/usage` headless: a local command, no model
call, no usage spent, about 3 seconds. The numbers are the account's, from
every session. It prints one line, such as

    level normal: 5h 33% (reset 15:50, window 36% gone); week 47% (reset Mon 2 Nov 22:00, 23% gone); extra off

and appends it to `STATE_DIR/usage.log`; `-j` gives JSON. Exit code 1 and
`level unknown` mean it could not read (offline). The script's header has
the thresholds.

| Level | The coordinator |
|---|---|
| `plenty` | max where it helps, up to the agent limit |
| `normal` | max for hard problems only (Lean proofs, concurrency, algorithm design), high otherwise |
| `tight` | high only, at most two agents at a time, puts off what can wait, tells Frans once if he is there |
| `limit` | starts nothing; sets a one-off check-in (CronCreate, not recurring) 3 minutes after the reset the line gives; writes the limit in the events |
| `unknown` | keeps the last known level; the next check-in reads again |

Run it at the start, at every check-in, and before starting an agent at
max or a second agent at a time, if the last reading is more than 20
minutes old. Frans's word overrides the level ("usage is tight", "plenty
of usage") until he says otherwise; write it on the Usage line.

A weekly limit that is reached stops the work until its reset, days away:
write `news.md` (`needs a look`) and tell Frans.


The watchdog
------------

    nohup caffeinate -i sh SKILL_DIR/watchdog.sh STATE_DIR PID "YYYY-MM-DD HH:MM" >/dev/null 2>&1 &

PID is this session's process ID; the time is when Frans is back. It keeps
the Mac from idle sleep and logs to `STATE_DIR/watchdog.log` every 5
minutes. It writes `news.md` once if the session process is gone. At its
end, it writes once if the heartbeat is more than an hour old. It never
restarts anything. Its header has the details.


Rules
-----

* **Answer quickly.** Your own turns are a few quick tool calls. Run
  builds, gates, Lean, measurements and reviews as background commands or
  in subagents, never in the foreground.
* **Subagents.**
  * Use background agents (Agent). Pass `effort` on every call: `max` for
    hard problems (Lean proofs, concurrency, algorithm design) or when
    usage is plentiful; `high` for mechanical work or when usage is
    tight.
  * Write the agent's name or ID, task, item, clone, effort and output
    file in the state file at once.
  * The brief: as for a peer who knows nothing of the conversation; it
    names the item, the clone, the files it may write, when to stop, and
    a report of about 20 lines, the rest in the item's State note.
* **The session's effort follows the mode** (section "Effort"): xhigh
  attended, max unattended.
* **Usage.** Pace by `USAGE`'s level (section "Usage"), or by Frans's
  word when he gave one. A usage limit reached goes into the events with
  its times.
* **Shared things.** Today's coordinator owns:
  * commits to `main`, in Frans's name, with no AI attribution;
  * new numbers in shared item series;
  * heavy runs, one at a time;
  * the summary in `news.md`.

  Other sessions report to it. Stage only right before committing, and
  commit with a path list; the Git index is shared.
* **Preserve** other sessions' uncommitted edits and Frans's files. Ask a
  session before touching what its open entry covers.
* **State before the turn ends.** Whatever another session would need to
  continue goes into `state.md` or the day's plan before the turn ends.
* **Frans's own sessions** suit work he wants to follow and think along
  with. Suggest one when a task is of that kind, instead of a subagent.
