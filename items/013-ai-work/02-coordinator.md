# 013-02 The daily coordinator

Created 2026-10-28 by Claude (Opus 5.5, Claude Code), at Frans's request.
Status: open.

This describes how Frans works with one AI session, the *coordinator*. He
talks to it, and it runs most of the work through subagents, whether he is
at the machine or not. It is written for Frans, for Claude, and for any
other AI agent asked to coordinate. It comes from a conversation on 28
October 2026 and builds on 013-01: the unattended night is one of the
coordinator's modes.

What Frans asked for:

> Sometime I want interaction when I sit and work. Then I prefer answers
> quickly. But there are hard long-running work that should go on
> unattended as far as possible.

> A new coordinator once a day sounds good. In the morning, I can look at
> news.md, finish things in the coordinator started the day before. Once
> that is done, I start a new coordinator for the new tasks. They may even
> run in parallell in the morning with the older one closing tasks and the
> new one creating new tasks.

> In any case, the coordinator must continue its work when access and
> usage has been restored. Even if it runs out of Claude usage or if the
> Internet connection goes down.

Claude Code's tool names are given in parentheses. Another agent uses
whatever does the same job. The Claude Code implementation, a skill and a
watchdog script, is described in section 10.


## 1. The idea in brief

* **One coordinator a day.** Frans talks to it. It does little work
  itself, so that it can answer quickly; subagents and background commands
  do the long work.
* **Three modes**, which Frans switches:
  * *attended* while he works with it;
  * *unattended* while he is away, for an hour or a night (013-01);
  * *closing* the next morning, when a new coordinator has started.
* **A new coordinator each morning.** Yesterday's closes its open tasks
  while today's takes new ones. They may run side by side for a while.
* **Frans's own sessions** are for work he wants to follow and think
  along with. They report to the coordinator.
* **The state is in files.** A fresh session can take over in a minute,
  and the work goes on after a usage limit or a network outage.

Why one session across modes, and not one session for the day and another
for the night:

* Subagents belong to the session that started them. Only that session
  gets their reports and can resume them after a usage limit. A night
  session cannot take over the day's agents.
* A handover in the evening comes when Frans is leaving and has the least
  time to check it. The session that knows the work asks him the open
  questions and goes on. The handover between coordinators is in the
  morning instead, while Frans is there.
* A new session each day keeps the context short. A long context makes
  every answer slower and loses detail when it is compacted.


## 2. Roles

| Who | Does |
|---|---|
| Frans | Starts the day's coordinator, switches its mode, decides. |
| Today's coordinator | Talks with Frans, plans, briefs and checks subagents, owns the shared things (section 6), writes the day's plan and `news.md`. In unattended mode it is 013-01's lead session. |
| Yesterday's coordinator | In closing mode: finishes or hands over its open tasks, starts nothing new. |
| Subagents (Agent) | One task each, in a scratch clone of their own, from a brief that points to an item. They write their state into the item and report back briefly. They do not commit to `main`. |
| Frans's own sessions | Work he wants to follow. They use scratch clones, report finished files to the coordinator, and ask it before heavy runs. |
| The watchdog | A shell script outside the session, started for unattended mode: keeps the Mac awake, logs whether the session lives and the network works, and writes `news.md` if the session is gone (section 8). |
| The conductor | 013-01's script for the night's timed steps. |
| `night.sh` | The nightly test run, from launchd at 02:10. Left alone. |


## 3. The day

1. **By 07:00.** Yesterday's coordinator has written the night's summary
   in `news.md` (013-01, section 8).
2. **Morning.** Frans reads `news.md` and settles what needs him in
   yesterday's coordinator: decisions, questions, finishing touches.
3. **Frans starts today's coordinator.** He opens a new session, in the
   bergdb repository, and types `/coordinator`. He names the session
   `coord-MMDD`, for example `coord-1029`. Today's coordinator:
   * makes its state directory (section 7);
   * tells yesterday's coordinator to switch to closing;
   * takes over the shared things;
   * sets its check-in;
   * tells Frans in a few lines what is open.
4. **The day.** Attended mode while Frans works with it.
5. **When Frans leaves**, for an hour or for the night: "I'm leaving until
   07:00". The coordinator switches to unattended (section 4.2).
6. **When Frans is back**: "I'm back". The coordinator gives a short
   summary and switches to attended.
7. **The next morning**, a new coordinator starts, and this one switches
   to closing (section 4.3). When it is done, Frans closes it.

Frans need not use all of this every day. A day without unattended work is
attended only, and a coordinator may run a day or two before a new one
starts.


## 4. The modes

The mode is written in the state file. Check-ins read it there.

### 4.1 Attended

* **Answer first, and quickly.** The coordinator's own turns are short: a
  few quick tool calls. A turn that takes minutes makes Frans wait.
* **Delegate everything long** (section 5): builds, gates, Lean, reading
  many files, measurements, reviews.
* **Ask when unsure.** The decisions are Frans's.
* **Report results briefly** as they come in: one or two lines and where
  the details are. The details belong in the item.
* **No timed runs.** Frans's own activity disturbs them. Timed runs wait
  for the quiet block (013-01, section 7).
* **Check-in every hour**, so that stopped work resumes even if Frans
  steps away (section 8).

### 4.2 Unattended

**Switching.** Frans says that he is leaving and when he will be back.
Before he goes, the coordinator:

1. asks the questions that would otherwise stop the work (013-01,
   section 3, step 4), in one round, and quotes the answers in the day's
   plan;
2. writes in the plan what will run while he is away, and when;
3. starts the watchdog until his return (section 8);
4. sets the unattended check-in, every 20 minutes;
5. confirms in two or three lines.

**While Frans is away**, the coordinator works as 013-01 describes:
* subagents in clones;
* gates and commits, as far as Frans allowed;
* `news.md` entries;
* for a night, the quiet block with the conductor.

A question that comes up goes on the list "For Frans to decide", with a
recommendation, and the work goes on with something else.

**Permissions.** The session must run in a permission mode that does not
stop for prompts (auto mode in Claude Code). A prompt left open stops the
coordinator until Frans returns.

**When Frans is back**, the coordinator:

1. gives a summary of at most ten lines: what was done, what failed, and
   a numbered list of decisions, each with a recommendation;
2. stops the watchdog;
3. sets the attended check-in.

### 4.3 Closing

Yesterday's coordinator switches to closing when today's starts, or when
Frans says so. Then it:

1. **Starts nothing new.** New requests go to today's coordinator.
2. **Ends each open task** in one of two ways:
   * it finishes the task. It gates the change and reports the files and
     gate results to today's coordinator (SendMessage), which commits;
   * or it hands the task over. It writes the task's State note in its
     item and names the task to today's coordinator, or registers it as a
     005 entry.
3. **Writes the plan's Outcome** and a `news.md` entry if anything
   changed since the morning summary.
4. **Cleans up.** It deletes its check-ins (CronDelete), stops its
   watchdog, and sets its mode to `closed` in the state file.
5. **Tells Frans** that the session can be closed.


## 5. What the coordinator does itself

| Work | Done by |
|---|---|
| Talking with Frans, planning, deciding what to delegate | The coordinator |
| Briefing subagents, reading their reports, checking the claims that matter (gate output, diffs, numbers) | The coordinator |
| Small edits: a plan line, a progress entry, a news entry | The coordinator |
| Commits, in Frans's name, with no AI attribution | The coordinator |
| A task of more than a few minutes, with a clear "done when" | A subagent |
| Gates, builds, measurements | A background command, or the subagent that needs them |
| Work Frans wants to follow and think along with: design questions, learning, decisions with much back and forth | Frans's own session. The coordinator suggests one when a task is of this kind. |

**Briefs.** Each brief is written for a peer who knows nothing of the
conversation. It names:
* the item, which holds the task;
* what is known or ruled out;
* the clone;
* the files in the main tree the agent may write;
* when to stop;
* how long the report may be: about 20 lines, the rest in the item.

Short reports keep the coordinator's context small.

**State notes.** A subagent keeps a short State note in its item: what is
done, the clone, the next step. A new agent can then continue from it.

**Limits.** At most the number of subagents Frans allows at a time;
fewer when usage is tight (section 9).


## 6. The shared things: one owner

Several sessions share the main tree, the Git index, the CPU and
`news.md`. Today's coordinator owns:

* **commits to `main`.** Other sessions report finished, gated files to
  it, with their hunks of shared files, and it commits them;
* **new item numbers** in shared series such as 005 and 006. A session
  asks it before taking one;
* **heavy runs**: the four gates (about 45 minutes on all cores), timed
  runs, and anything that loads the machine for long. They run one at a
  time; a session asks before starting one;
* **the summary in `news.md`**. Any session may add its own entries with
  `tools/news.sh`.

The ownership passes when today's coordinator starts. From then on,
yesterday's reports to it like any other session.

A message between sessions (SendMessage) may wait for Frans's approval if
the two sessions run in different permission modes. Run the coordinator
and the sessions that report to it in the same mode.


## 7. The state

Two places:

* **The day's plan** is a subitem of the quarter's item, such as 006-10.
  It is made when the first task is delegated. Its sections follow
  013-01, section 3, step 3: the requests, quoted, with Frans's answers;
  the ground rules; the tasks; the timeline; the progress, with times
  from `date`; and the Outcome. This is the record. It is committed.
* **The state file**, `/Users/f/fl/bench/coord/YYYY-MM-DD/state.md`
  (from the skill's template). It is not in a repository. It holds what
  changes by the minute:
  * the mode;
  * the session's name, ID and process ID;
  * the plan's ID;
  * the agents, with their tasks, clones and status;
  * the background commands;
  * the check-in jobs and the watchdog;
  * the usage;
  * what waits for Frans;
  * the events.

  It lives outside `/tmp`, so that a restart does not remove it. The
  same directory holds the check-ins' `heartbeat` file and the
  watchdog's log.

**The rule:** whatever another session would need to continue goes into
one of the two before the turn ends.


## 8. Usage limits, network outages and a dead session

Three things can stop the coordinator: the 5-hour usage limit, the network,
and the session itself.

**A usage limit or a network outage.** The session stays open, but every
call to Claude fails:

* subagents stop with an error (HTTP 429, or a connection error);
* the coordinator's turn ends with an error;
* background commands go on, since they run locally. Their notifications
  may be lost while the session cannot answer.

The *check-in* brings the work back. It is a recurring prompt that the
session schedules for itself (CronCreate):

* It fires whenever the session is idle, also after an error. While the
  limit or the outage lasts, each check-in fails too. The first one after
  access returns runs.
* It is cheap when all is well:
  1. touch the heartbeat;
  2. read the state file;
  3. look for interrupted work, and end in one line.
* When something was interrupted, it resumes it:
  * a subagent that stopped without its report is resumed with a message
    (SendMessage). It continues from its transcript;
  * a background command is judged by its process and its output file,
    not by a notification;
  * the timeline of the plan goes on.
* After a pause, it writes one progress line with the pause's times. The
  heartbeat gives the start, and the watchdog's log tells whether the
  network was down (otherwise the cause was likely the usage limit).
* When the coordinator sees the limit coming (level `limit`, section 9),
  it knows the reset time. It sets a one-off check-in 3 minutes after the
  reset, so the work resumes then and not at the next regular check-in.

| Mode | Check-in | Note |
|---|---|---|
| Attended | every hour | |
| Unattended | every 20 minutes | With a night's quiet block, only from 06:00 to 21:59, so that no check-in runs in the block. |

The scheduler delays each recurring job by a fixed amount, up to half its
period. So in unattended mode, work resumes within about half an hour of
access returning. Recurring jobs expire after 7 days, which is no problem
with a new coordinator every day.

**A dead session.** VS Code closed or crashed, the machine restarted, or
the process was killed. The check-ins lived in the session and are gone
with it.

* The watchdog notices that the process is gone. It writes `needs a look`
  in `news.md` once.
* The conductor's night steps run anyway (013-01, section 7).
* To continue:
  1. Frans resumes the session: from VS Code's session list, or with
     `claude --resume <session ID>` in a terminal. The ID is in the state
     file.
  2. He types `/coordinator resume`. The coordinator then:
     * sets the check-in again;
     * restarts the watchdog for the new process;
     * restarts stopped subagents from their items' State notes;
     * writes the gap in the progress.

  This step is not automatic yet (section 11).

**The machine's sleep.** The watchdog runs under `caffeinate -i`, which
keeps the Mac from idle sleep while it runs.


## 9. Effort and usage

* **The coordinator's effort follows its mode** (Frans, 2026-10-28):
  * attended: xhigh, which gives quicker answers. Frans finds it better
    for interaction than max;
  * unattended: max, where speed does not matter, unless the usage level
    is tight;
  * closing: xhigh.

  xhigh is the default for Opus 5.5 in `~/.claude/settings.json`
  (`modelSettings`), so a new session starts there. `/effort LEVEL`
  switches for the session only and leaves the settings alone. Claude
  Code sends the effort inside the conversation, so a switch keeps the
  prompt cache. A max turn costs about twice an xhigh one (Claude Code's
  effort cost index for Opus 5: high 1, xhigh 1.66, max 3.44).

  Frans switches the effort; the coordinator cannot. A scheduled prompt
  (CronCreate) of `/effort xhigh` reached the model as plain text, not as
  the command (tested 2026-10-28, 13:03). So the coordinator ends its
  switch to unattended with "type `/effort max`", and its switch back with
  "type `/effort xhigh`". If he forgets, little is lost: the heavy work is
  done by subagents, whose effort the coordinator sets on every call.
* **Subagents get their effort set on every call** (Frans, 2026-10-27):
  * max for hard problems (Lean proofs, concurrency, algorithm design),
    or when usage is plentiful;
  * high for mechanical work, or when usage is tight.
* **The usage, read by the coordinator itself.** The plan has a 5-hour
  window and a weekly one. `skill/usage.sh` runs Claude Code's `/usage`
  headless (`claude -p /usage`). That is a local command: it calls no
  model, spends no usage, and takes about 3 seconds. Its numbers are the
  account's, from every session and machine. The script prints one line
  with a level, for example:

      level normal: 5h 33% (reset 15:50, window 36% gone); week 47% (reset Mon 2 Nov 22:00, 23% gone); extra off

  A week "ahead of its time" means its use minus the share of the week
  gone. On 28 October at 12:39 the week was 47 % used with 23 % gone: 24
  points ahead, so normal, one point short of tight.

  | Level | When | The coordinator |
  |---|---|---|
  | plenty | 5h below 50 %, and the week at most 15 points ahead of its time (Frans, 2026-10-28) | max where it helps, up to the agent limit |
  | normal | otherwise | max for hard problems only, high otherwise |
  | tight | 5h at 80 % or more; or the week at 85 % or more, or 25 points ahead of its time; or the server warns | high only, at most two agents, puts off what can wait |
  | limit | 5h or the week at 98 % or more | starts nothing; a one-off check-in 3 minutes after the reset resumes the work |

* **When the level is read:**
  * at the start;
  * at every check-in, logged in the state directory's `usage.log`;
  * before starting an agent at max, or a second agent at a time.

  A night's `usage.log` shows how much each part of the work used.
* **Frans's word overrides the level** ("usage is tight", "plenty of
  usage") until he says otherwise.


## 10. The Claude Code implementation

The files are in [02-coordinator/](02-coordinator/):

* [skill/SKILL.md](02-coordinator/skill/SKILL.md), the `coordinator`
  skill. It holds the procedures for each mode and for the check-in.
* [skill/state-template.md](02-coordinator/skill/state-template.md), the
  state file's template.
* [skill/watchdog.sh](02-coordinator/skill/watchdog.sh), the watchdog.
* [skill/usage.sh](02-coordinator/skill/usage.sh), the usage and its
  level (section 9).

The skill is installed for every Claude Code session on F53 by a link,
so that sessions started in bergdb, f1 or elsewhere all see it:

    ln -s /Users/f/fl/repos/bergdb/items/013-ai-work/02-coordinator/skill \
        ~/.claude/skills/coordinator

| Command | What it does |
|---|---|
| `/coordinator` | Starts today's coordinator in this session. |
| `/coordinator unattended until 07:00` | Switches to unattended mode. "I'm leaving until 07:00" does the same once the skill is loaded. |
| `/coordinator attended` | Switches back to attended mode, as does "I'm back". |
| `/coordinator closing` | Switches to closing mode. |
| `/coordinator check-in` | The check-in, normally fired by the session's own scheduled job. |
| `/coordinator resume` | After the session was restarted. |

The Claude Code tools it uses:

* **Agent**, for background subagents with their effort set;
* **SendMessage**, to resume subagents and to talk to other sessions;
* **ListAgents**, to find the sessions;
* **CronCreate**, **CronList** and **CronDelete**, for the check-ins;
* **Bash** with `run_in_background`, for gates and measurements.

`~/.claude/sessions/<pid>.json` gives a session's name, ID and whether it
is busy.


## 11. Open points

* **Automatic revival.** `claude --bg --resume <session ID>` continues a
  session in the background under the same ID. The watchdog could use it
  to revive a dead coordinator and send it `/coordinator resume`. This is
  not tested. A revived session also needs a permission mode that does
  not stop for prompts.
* **The usage thresholds** in `usage.sh` are a first guess. Adjust them
  after a few days of `usage.log`. The shape of `/usage`'s structured
  report (`usage_report.rate_limits`) is marked experimental in Claude
  Code. If it changes, the script says `level unknown` and the
  coordinator keeps its last level.
* **Lessons.** After the first week, write the lessons here, as 013-01,
  section 9 does for the night.
