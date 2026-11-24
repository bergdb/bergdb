# 013-04 The lead

Created 2026-11-23 by Claude (Opus 5.5, Claude Code), at Frans's request.
Status: open.

The *lead* is the AI session Frans works with: he talks to it, and it runs
most of the work through subagents, Codex and detached runs, so that it can
answer him at once. This describes it for Frans, for Claude, and for any
other AI agent asked to lead. Claude Code's tool names are given in
parentheses; another agent uses whatever does the same job. The Claude Code
skill `lead`, [04-lead/skill/](04-lead/skill/), implements it; this
description gives its reasons and the facts it rests on, and is kept up to
date with it.

The lead is 013-02's coordinator under a new name (Frans, 2026-11-23) and
takes the role of 013-01's lead session. A lead needs nothing from 013-01
or 013-02; they are kept as the record of the first nights and of the
coordinator (2026-10-28 to 2026-11-22), and 013-01 as the home of the
conductor. The skill was cleaned up by [04-lead/plan.md](04-lead/plan.md),
the plan of 2026-11-23, which keeps the reasoning in full.


## 1. The idea in brief

What Frans asked for (2026-11-23):

* The lead coordinates the work through subagents and stays responsive to
  him. It often starts in the morning and runs until 07:00 the next
  morning; it may run several days when he says so.
* The skill is as short as possible. What matters most is that the lead
  works when Frans is at neither the computer nor the phone.
* The lead consumes at most 50 % of the week's usage; Frans changes the
  number during the week (section 6).
* Model and effort: the lead session typically Opus xhigh, set by Frans;
  subagents Opus xhigh, Opus high or Fable high (section 9). Codex is a
  kind of subagent: second opinions, reviews, and work when Claude's usage
  is tight.
* **No modes.** When Frans writes, the lead answers and plans with him;
  when he does not, it works from the plans in the documents. The lead
  never needs to know which, so nothing detects his presence.
* **One rule for decisions**, in three classes, the same whether he is
  there or not (section 4).
* **07:00 on weekdays** is the fixed point to stop and consolidate
  (section 5).
* No phone notifications, for now.
* Frans can override any of this.

Why one session for the day and the night, not one for each: subagents
belong to the session that started them, and only it gets their reports
and can resume them after an error; and a handover in the evening would
come when Frans is leaving and has the least time to check it. Why a new
lead now and then: a long context makes every answer slower and loses
detail when it is compacted. A lead runs until Frans closes it.

Why scripts: the coordinator's skill grew to 349 lines because the model
carried the mechanism. It switched modes by procedure, started and stopped
the watchdog, replaced check-in jobs, compared heartbeat times and read
usage levels from a table; its state files grew to 600 lines that every
check-in read again. Since the cleanup the mechanism is in three scripts
and the skill holds rules, in at most 120 lines:

* `status.sh`, the first call of every turn that Frans did not start,
  says what is due (section 3);
* `watchdog.sh` runs outside the session for the lead's whole life and
  acts where the model cannot: a dead or silent lead, the limit
  (section 10);
* `usage.sh` reads the usage and the limit (section 6).


## 2. Roles

* **Frans** starts a lead (`/lead`), talks to it, settles the decisions
  that wait for him (class 3) and those that went ahead by default, and
  closes a lead.
* **The lead** plans with Frans, briefs and checks subagents, runs Codex
  and the run scripts, lands the work, owns the shared things (section 7),
  and writes the plan and `news.md`.
* **A closing lead** ends its open tasks and starts nothing new
  (section 5).
* **Subagents** (Agent): one task each, in a clone of their own, from a
  brief that points to an item. They keep a State note in the item, report
  back briefly, and do not commit to `main`.
* **Codex** (OpenAI's Codex CLI, its own quota) runs detached in a clone of
  its own; its sandbox cannot commit (section 9).
* **Frans's own sessions** do work he wants to follow and think along
  with. They use scratch clones, report finished, gated files to the lead,
  and ask it before heavy runs. The lead suggests one for a task of that
  kind.
* **The watchdog**, `watchdog.sh`, outside the session (section 10).
* **`night.sh`, `week.sh` and `timing.sh`**, the run scripts, which the
  lead starts as steps of its plan (section 9).


## 3. The status line and the lines in capitals

`status.sh STATE_DIR` is the first call of every turn that Frans did not
start: a check-in, an agent's report, a finished command. It prints one
line, such as

    2026-11-24 22:37 Tue; week 33 %, limit 50 %: ok; watchdog up; disk 212 GB; next summary Wed 07:00

(the time; the usage, the limit and the level, section 6; whether the
watchdog runs; the free disk; the next summary not yet written), and a line
in capitals for each thing due. It appends both to `STATE_DIR/status.log`,
whose age is the lead's heartbeat, and changes nothing else. Its header
gives each line's exact form. What the lead does:

* **`STOP`**: the file `STATE_DIR/STOP` exists (the watchdog writes it at
  the limit), or the level is `stop` and the file is not there yet. The lead
  starts and resumes nothing on Claude, whatever the other lines say (a
  resume after a `PAUSE`, or a `DUE` that needs Claude, waits); running
  agents stop at their next step by their briefs (section 9). It lands what
  is gated, writes `news.md` once, and goes on only with runs and Codex.
  When the line has gone (the limit raised or the week reset), it starts the
  stopped tasks again from their State notes.
* **`PAUSE A to B`**: `status.log` was more than 45 minutes old, so no
  wake-up happened in between: the account's limit, the network, or a hung
  turn. The network's state from `watchdog.log` follows. The lead writes a
  line in the plan's progress with the times and the cause, and resumes
  each agent that stopped on an error as section 9 says (not under
  `STOP`, nor after a failed authentication).
* **`DUE`**: the time of a line in `pending`, a class 2 decision, has
  passed. Unless Frans has answered, the lead goes ahead with the default,
  within the level (no Fable agent at `tight`; at `stop` nothing new on
  Claude, while runs and Codex go on), records it on the plan's list of
  decisions as "by default" with the time, and removes the line. `DUE ?`
  marks a line that does not parse: the lead mends it, and no default goes
  ahead before its time is known.
* **`SUMMARY DUE`**: on a weekday from an hour before the summary's time
  (07:00, or `STATE_DIR/summary-time`) until the lead touches the day's
  marker `STATE_DIR/summary-YYYY-MM-DD`; only for a lead that ran before
  that hour that day. The lead writes the summary (section 5) and touches
  the marker.
* **`WATCHDOG GONE`**: no live watchdog, and the lead is not closed. The
  lead starts it again.
* **`DISK LOW`**: under 40 GB free. The lead deletes run data it made and
  starts no run that writes much.
* **`PERMISSION MODE`**: the lead's transcript shows a permission mode
  other than auto, so a permission prompt would stop the session. The mode
  is Frans's to set: the lead tells him in the chat and writes `news.md`
  once.

Then the lead looks at its agents and commands (section 9), carries the
plan on, landing before starting, and ends in one line when all is on
track. A wake-up when nothing is due is one script call and one line; its
cost in usage is measured on the first night.


## 4. Decisions in three classes

The lists are in the skill, section "Decisions": class 1, what the lead
decides; class 3, what waits for Frans. Any other decision is in class 2.
They are lists, not judgment, so that the lead decides the same way at any
hour, and Frans knows in the morning what went ahead without him. Frans
chose them on 2026-11-23 (plan, section 13, choices 1 to 4).

* **Class 1** goes into the plan and the lead goes on. A push to `main` is
  class 1 at any hour, after the gates and the privacy check, though a
  push cannot be taken back: the checks are the same at any hour.
* **Class 2 goes ahead by default.** The lead states it in the chat with a
  recommendation, "I go ahead with A at HH:MM unless Frans says otherwise",
  at least 30 minutes ahead, an hour as a rule, later when undoing costs
  more. It writes the full text on the plan's list of decisions and a line
  `YYYY-MM-DD HH:MM NAME: DEFAULT` in `STATE_DIR/pending`. The 30-minute
  check-in meets the deadline: `status.sh` prints `DUE` at the first
  wake-up after HH:MM, up to half an hour late, never early; when lateness
  matters, the lead also sets a one-off check-in at HH:MM. If Frans
  answers first, his answer decides and the line goes. What went ahead by
  default Frans can undo at the next 07:00; a decision that could not be
  undone then is class 3. Over a weekend the defaults add up until Monday
  07:00. A Fable agent is class 2.
* **Class 3 waits for Frans**: the lead writes the options and a
  recommendation on the plan's list, parks the task and goes on with
  other work.
* **Wider authority for a day.** Frans may let the lead decide something
  of class 2 or 3 tonight. The lead records it in the plan as a dated
  decision; it ends at the next 07:00 unless he says otherwise.

The plan's list of decisions is updated when a decision is stated, goes
ahead or is settled, so that it is current at any hour.


## 5. The cycle, closing, and leads of several days

* **07:00 on weekdays.** By 06:45 the lead has written, in the plan and as
  one `news.md` entry that points to it: what was done; what went ahead by
  default; the class 3 decisions that wait; its proposal for where to go
  next. Agents get stop times of 06:00 at the latest, so that Frans meets
  landed work and a clean main tree. At the summary the lead checks that
  exactly one check-in job exists.
* **Mornings** are planning together: Frans settles the decisions and the
  next plan.
* **When Frans writes at another time**, also from the phone, the lead
  answers and adds the same four things in short form, at most ten lines.
* **When the agreed plan runs out**, the lead takes open 028 entries that
  need no decision and that no other session owns (it checks first), or
  stops and waits for 07:00. It invents no new direction.
* **Friday's plan lasts until Monday 07:00.** At Friday's planning the
  lead says whether the plan's work and the room below the limit cover the
  weekend, and proposes more if not. No summary on Saturday and Sunday; a
  failure reaches `news.md` when it happens.

**A lead runs until Frans closes it**, not until 07:00. After a morning's
planning he goes on with the same lead or starts a new one. Several days
differ in little, since the cycle is the same every day: one plan for the
lead's life, with the progress under dated headings; `night.sh` once a day
while code lands; at the week's reset the limit is 50 % again and the
watchdog removes `STOP`. The lead makes the check-in job again when it is
five days old, at a summary; it would expire after 30 days (section 11),
and were it lost, the watchdog would report a silent lead.

**`/lead` in a session that has a state directory repairs** instead of
starting: the process ID in `state.md`, exactly one check-in job, the
watchdog (a new one for the new process replaces that of the old), then
`status.sh`, and, as its lines allow (no agent under `STOP`), after a
restart of the session's process, a new agent from the State note for each
agent listed as running (the old process's agents are gone); the gap goes
into the plan's progress.

**Closing** starts when Frans says so, or when a new lead starts and tells
the old one. The lead touches `STATE_DIR/closing` and then:

1. starts nothing new;
2. ends each open task: it lands it, or, when a new lead has started,
   sends that lead the branch, the head and the gate lines; or it hands
   the task over with a State note and a 028 entry;
3. keeps agents that are near their end until they report (agents cannot
   move to another session), with its check-in;
4. writes the plan's Outcome and a `news.md` entry;
5. deletes its check-in, touches `STATE_DIR/closed` (the watchdog ends),
   and tells Frans that the session can be closed.


## 6. The weekly limit and the levels

**What it counts.** The row `weekly_all` of Claude Code's `/usage`: the
account's week over all models, from every session and machine, Frans's own
sessions included. Codex has its own quota. The limit is a ceiling on that
figure, not a budget of the lead's own. The row `weekly_scoped` is a weekly
limit scoped to one model or surface, named by its model: on 2026-11-23,
Fable's week alone, the screen's "Current week (Fable)". `usage.sh` prints
every row; the limit applies only to `weekly_all`.

**Where it is stored.** One file for all leads,
`/Users/f/fl/bench/lead/limit`: the percent, the reset of the week it was
set in, and when it was set (`usage.sh`'s header has the format). Only
Frans raises it (class 3). When he names a number, the lead runs
`usage.sh -L N` and answers with the status line, which shows the limit.
`usage.sh` reads the file on every call, so every check-in, every new lead
and the watchdog see the latest value. Missing, unreadable, or from an
earlier week: 50 % (Frans chose the reset to 50 %, 2026-11-23, choice 5,
so that a high limit of a week's last day does not govern the next week).

**The levels:**

* `ok`: more than 10 points below the limit.
* `tight`: within 10 points. New agents run Opus high, at most two at a
  time, no Fable; landing comes before starting; a task that fits Codex
  goes there.
* `stop`: at or above the limit. Nothing new starts on Claude; running
  agents stop at their next step. The lead lands what is gated, writes
  `news.md` once, and goes on only with the runs and Codex.
* `unknown`: no row `weekly_all` (offline, or the report changed).

**The stop does not depend on the model.** In every round of five minutes
the watchdog reads the usage (`usage.sh` calls no model) and, at `stop`,
writes `STATE_DIR/STOP`, so that the file comes within ten minutes of the
limit, the time of the calls included (the plan said every ten minutes,
which with that time could come later). It removes the file when the usage
reads below the limit again (the limit raised, or the week reset), and only
a `STOP` it wrote. An hour of unreadable usage also gives `STOP`, until it
reads again. Each agent's brief says: look for `STOP` before every long
step; if it is there, write the State note, commit in the clone and report.
The week may pass the limit by a point or two. (The coordinators wrote such
a watch by hand on several days, 006-32.)

**The account's own limit** (the week at 100 %, an error 429): every call
fails until the reset; the first wake-up after it prints `PAUSE` (after a
gap of more than 45 minutes), and the lead resumes its agents; an agent
that ended on an error in a shorter gap is resumed at the next wake-up
(section 9). **The 5-hour window** has not been in `/usage`'s report since
2026-11-08; the lead does not pace by it. **What 50 % buys:** an agent cost
roughly one point of the week per hour in November, so three agents reach
the limit within a day and a night; seven Fable subagents took about 10
points an hour (2026-11-11).


## 7. Clones, gates and commits

**The shared things have one owner, the lead:**

* commits to `main`, and pushes. Other sessions report finished, gated
  files to it, with their hunks of shared files, and it commits them.
  `origin` is the public github.com/bergdb/bergdb (since 2026-11-17): a
  pushed commit is public at once, and `main` refuses force pushes;
* new numbers in shared series such as 006 and 028; a session asks the
  lead before taking one;
* heavy runs on F53 (section 9);
* the summary in `news.md`; any session may add its own entries with
  `tools/news.sh`.

The ownership passes when a new lead starts. Run the lead and the sessions
that report to it in the same permission mode: a message between sessions
(SendMessage) may otherwise wait for approval.

**Clones.** Code and Lean work is done in scratch clones, such as
`/Users/f/fl/bench/<date>/<task>/`. The main tree takes finished, gated
changes only, by cherry-pick or copy. Check first that `java/` and `lean/`
in `main` have not changed since the clone's base; if they have, rebase
and gate again.

**Gates.** A change to `java/` needs `java/before-commit.sh` (`BEFORE
COMMIT OK`) and the level script of the mechanism it changes (`level2.sh`
to `level4.sh`); a change to `lean/` a clean `lake build`, with no `sorry`
and no new axiom. Gate the combined tree, with the day's earlier changes in
it. AGENTS.md, "Code", says which work needs more.

**Commits.** In Frans's name, with no AI attribution, by the lead only.
Before each commit, check the change for private data (AGENTS.md, "Public
repository"). Commit only this work's files or hunks, never another
session's uncommitted edits. The Git index is shared by all sessions:
stage right before committing, and commit with a path list.

**Principles.** Every task is checked against 010-01; a departure is
written there, under its principle.

**Raw output** of test runs does not go into the repository (Frans,
2026-10-28): keep the scripts, the summary tables and the findings in the
item.


## 8. The plan and the state

**The plan** is a subitem of the quarter's item, such as 006-33: one for
the lead's life, made when the first task is delegated, its number taken
from the main tree right before it is written. Its sections:

1. the requests and Frans's decisions, as dated facts;
2. the ground rules, where they differ from section 7, and what happens
   if the session stops: which runs go on detached, and the State notes
   the work restarts from;
3. the tasks, W1 to Wn, each with its "done when" and the principles
   (010-01) it must keep;
4. the timeline;
5. the list of decisions: class 2 with its time and default, what went
   ahead by default, class 3 with the options and a recommendation;
6. the progress, under dated headings, with times from `date`;
7. the Outcome, at closing.

It is the record. It is committed, and so public: it records decisions,
reasons and conclusions, not the conversation (AGENTS.md, "Public
repository").

**The state directory**, `/Users/f/fl/bench/lead/YYYY-MM-DD` (the lead's
first day; `-2` for a second lead that day), outside `/tmp` so that a
restart does not remove it, holds:

* `state.md`, from the skill's template: only what is live, the session's
  name, ID and process ID, the plan's ID, the previous lead, the check-in
  job, the heavy runs, the running agents (task, clone, model, effort,
  output file, stop time), the background commands, and what comes next.
  The usage and the events are in `status.log` and the plan's progress;
* `pending`, the class 2 decisions, one line each;
* `status.log`, `status.sh`'s lines, the heartbeat;
* `STOP`, `closing`, `closed`, `summary-YYYY-MM-DD` and `summary-time`;
* the watchdog's `watchdog.pid` and `watchdog.log`.

**The rule:** whatever another session would need to continue goes into
`state.md` or the plan before the turn ends. A subagent keeps a short State
note in its item (what is done, the clone, the next step), so that a new
agent can continue from it.


## 9. Subagents, Codex and runs

**Model and effort** (Frans, 2026-11-23). The lead passes `model` and
`effort` on every Agent call; a subagent otherwise inherits the session's.

* **Opus xhigh**, the default: proofs, concurrent code, design, reviews,
  investigations.
* **Opus high**: ordinary programming with a clear "done when" and gates
  that catch mistakes, and every new agent at `tight`.
* **Fable high**: a proof that Opus xhigh failed at, or the plan of large
  work. One at a time, none at `tight`, and class 2.
* Never medium or low; max only when Frans asks.
* At most four agents at a time, two at `tight` (choice 7).
* The lead session's own model and effort are Frans's to set; the lead
  cannot change its own (section 11).

**Briefs** are written for a peer who knows nothing of the conversation.
Each names the item, which holds the task; what is known or ruled out; the
clone; the files in the main tree the agent may write; its stop time; the
`STOP` check of section 6; and a report of at most 20 lines, the rest in
the item's State note. Short reports keep the lead's context small. The
lead writes each agent in `state.md` at once.

**A stopped or stalled agent.** At every wake-up, unless `STOP` holds, an
agent that ended on an error (429, 529, the network; not a failed
authentication, below) instead of with its report is resumed (SendMessage;
it continues from its transcript); its error's notice starts a wake-up of
its own, or the next check-in finds it. One listed as running whose output
file has not changed for 30 minutes (`stat -L`: the file is a link), with
no command of its running, is told to continue or report; one past its stop
time, to write its State note and stop.

**Agents that cannot authenticate.** On 2026-11-13 an account change
stopped every subagent with "API Error: 403", while the session itself
worked; only Frans could fix it, by logging in again (`/login`). The lead
tests with one small agent; if that fails too, it writes `news.md` once
("log in again") and resumes nothing, and tests again at most once an
hour. When it works, it resumes the stopped agents.

**Codex** is used at any level for an independent review of a large or
delicate change before it lands and for a second opinion on a plan, and at
`tight` and `stop` for tasks with a clear "done when" that gates check. It
runs detached, in a clone of its own made for it and thrown away after,
from a prompt file, as in 020-14, section 1:

    cd /Users/f/fl/bench/<date>/<task>      # prompt.md here
    nohup codex exec -m gpt-6.1-sol -c model_reasoning_effort="high" \
      -c approval_policy="never" -s workspace-write -C <its clone> \
      -o report.md - < prompt.md > codex.log 2>&1 &

`workspace-write` lets it compile and run probes in its clone; it has no
network, and its sandbox cannot commit: the lead reads `report.md`, gates
and commits. When Codex stops on its own limit, the lead starts a waiter, a
detached command that resumes it at the retry time (`codex exec resume`
with the session's ID). When a content filter stops it, the task is not
reworded; it goes on the plan's list for Frans.

**Runs.**

* **Heavy runs**: up to six at once on F53 (Frans, 2026-11-13); a timing
  run alone. The lead counts them in `state.md`; other sessions ask it.
* **`night.sh`** (about 2.5 hours) and **`week.sh`** (about 10 hours, with
  `ANDROID_SDK` set) are functional: they may run beside other work, at a
  low priority if need be. The lead starts them from the main tree as
  steps of its plan, with the commands in their headers; they clone the
  committed code themselves. `night.sh` runs once a day while code lands;
  all three run before every release, on a commit near it (028-23,
  028-27).
* **`java/timing.sh`** needs a quiet machine. The lead starts it with
  `WAIT` as a detached command when its own heavy work has ended, and
  starts no agent and no other run on F53 until it ends (choice 10). On s1
  it checks `ps` first; other sessions time there too.
* **Smoke tests.** A script made for a run without Frans is tried first,
  and its output is checked, not only its exit code.


## 10. Robustness without Frans

What can stop or stall the lead, what handles it, and how it is tested.
`test/run.sh` is the scripts' test on canned inputs and stand-ins (a
`claude` that prints a canned `/usage` report, a limit file, `df`,
`tools/news.sh`, the session's process and files, an unreachable network);
it prints `LEAD TESTS OK` (2026-11-23: 101 checks, about a minute).

1. **A permission prompt or a dialog question** stops the session. The
   lead runs in auto mode and asks only in text; `status.sh` prints
   `PERMISSION MODE` when the transcript shows another mode. A refusal by
   auto mode is final, with no rewording. Tested: `run.sh` (modes default
   and plan give the line, auto not). Auto mode has worked nightly.
2. **A decision nobody answers.** Class 2 goes ahead on `DUE`; class 3 is
   parked (section 4). Tested: `run.sh` (`DUE` at its minute and after,
   not before; an unreadable line in `pending`), and the skill by a fresh
   agent (section 12, 2026-11-23).
3. **Frans's limit.** The watchdog writes `STOP` (section 6). Tested:
   `run.sh` (written at the limit, once; removed when the limit is raised
   and at the week's reset; a `STOP` by someone else stays; written after
   unreadable usage and removed when it reads again; a hung `/usage`
   stopped after `USAGE_TIMEOUT` and counted as not read, also when it
   printed its report first).
4. **The account's limit, errors 429 and 529, the network.** The first
   wake-up after a gap of more than 45 minutes prints `PAUSE` with the
   network's state, and the lead resumes its agents; after a shorter
   outage, the next wake-up resumes the agents that ended on an error
   (section 9). Tested: `run.sh` (`PAUSE` after 46 minutes, not 45;
   network down, up, no log, no rounds in the gap). Seen to work since
   006-09; outages were rare and minutes long in fifteen watchdog logs; a
   long one is not tested.
5. **Agents cannot authenticate** (section 9). Cannot be provoked:
   accepted as untested.
6. **The session is dead** (VS Code closed or crashed, the Mac restarted,
   the process killed). Its check-ins and agents are gone; detached runs go
   on. The watchdog writes `news.md` within ten minutes and ends; Frans
   reopens the session and types `/lead`, which repairs. The watchdog reads
   no usage once the process is gone, so a slow `/usage` does not delay the
   report. Tested: `run.sh` (reported once; reported at once while `/usage`
   hangs). Not seen by the watchdog in fifteen logs. A restart of the Mac
   kills the watchdog too: the missing summary is then the only sign.
   Automatic revival was not taken (choice 9).
7. **The lead does not wake**: its check-in job is gone, or a turn hangs.
   The watchdog writes `news.md` when `status.log` is 75 minutes old while
   the process lives, and again only after it was fresh. The lead keeps
   exactly one job, checked at every summary and repair. Tested: `run.sh`
   (reported once; a second silence reported again).
8. **The Mac sleeps, or the watchdog is gone.** The watchdog keeps the Mac
   from idle sleep (`caffeinate -i`; no gap over six minutes in fifteen
   logs; a closed lid still sleeps) and logs a gap in its own rounds.
   `status.sh` prints `WATCHDOG GONE`, and the lead starts it again; a
   second watchdog for the same directory and process exits at once, and
   one for a new process of the lead (after a restart) replaces the old.
   Tested: `run.sh` (a gap logged once; `WATCHDOG GONE` for a dead process
   or no pid file, not once closed; a second watchdog exits; one for a new
   process replaces the old).
9. **An agent stalls** (section 9). Seen to work.
10. **The disk fills.** `DISK LOW` under 40 GB. Tested: `run.sh` (39 GB
    gives the line, 40 GB not).
11. **The context is compacted.** What another session needs is in the
    state file or the plan before a turn ends. Seen to work (006-32).

`SUMMARY DUE` is tested by `run.sh` too: from 06:00 on a weekday until the
marker, not on Saturday and Sunday, at an hour from `summary-time`, and
not for a lead started after 06:00.

The rehearsal planned in plan section 9.2 was replaced by the first night
(Frans, 2026-11-23): the first night on the new skill does real work and is
the test. At night, when it disturbs no one, the lead stages a network gap
of 20 minutes that spans a check-in's minute, so that `status.sh` misses a
wake-up and its gap passes 45 minutes (`PAUSE` with "network down", a line
in the progress, the agents resumed) and a killed watchdog (`WATCHDOG GONE`,
a new one). `status.log` is the audit: a line at least every 35 minutes
outside the staged gap. The night's summary gives the cost of an idle
check-in.


## 11. The Claude Code facts the scripts rest on

Checked on 2026-11-23 on F53 (Claude Code 2.1.317 to 2.1.330) unless
dated otherwise.

* **`claude -p /usage`** with `--output-format stream-json --verbose` is a
  local command: no model call, no usage spent, about 3 seconds. Its
  `usage_report` carries the usage endpoint's rows, as the account sees them
  from every session and machine: `weekly_all`, `weekly_scoped` (a weekly
  limit scoped to the model in `scope.model.display_name`), `session` (the
  5-hour window, absent since 2026-11-08); `is_active` marks the server's
  headline row. A live reading on 2026-11-23 gave the same figures as the
  `/usage` screen. Claude Code marks the report's shape as experimental: if
  it changes, `usage.sh` says `unknown`, and after an hour the watchdog
  writes `STOP`. A call that takes over a minute is stopped and counts as
  not read, whatever it printed (`usage.sh`, since 2026-11-23), so that it
  holds up neither `status.sh` nor the watchdog.
* **`~/.claude/sessions/PID.json`** holds a running session's process ID,
  `sessionId`, `name`, `status` (busy or idle) and working directory.
* **The transcript** `~/.claude/projects/*/SESSION_ID.jsonl` records each
  prompt's `permissionMode`, and its origin in `turnOrigin` (`human`, also
  from the phone, against `scheduled`, `task_notification` and `peer`).
* **The session's ID** is the name of the directory above its scratchpad.
* **Check-ins** (CronCreate) live only in the session that made them and
  fire when it is idle, also after an error, so the first one after a limit
  or an outage resumes the work. Recurring jobs expire after 30 days (the
  tool's description, 2026-11-23; 013-02 recorded seven days). After a VS
  Code restart resumed in the same session, the old jobs lived on, and a
  new one fired as a second (2026-11-07): hence exactly one job at a
  repair.
* **The lead cannot change its own effort**: a scheduled prompt of
  `/effort xhigh` reached the model as plain text, not as the command
  (2026-10-28). `/effort` sets it for the session only.
* **Subagents** belong to the session that started them: only it gets
  their reports and can resume them (SendMessage), and they end with its
  process. A subagent stopped by an error continues from its transcript
  when resumed. Its output file is a link: `stat -L` gives its last
  activity.
* **Auto mode** lets the session run without permission prompts; a
  refusal by it is final. A dialog question (AskUserQuestion) waits for an
  answer, so the lead asks only in text.
* **SendMessage** between sessions may wait for approval when the two run
  in different permission modes.


## 12. Decisions and tests

Dated decisions in force (Frans's unless marked):

* 2026-10-28: raw output of test runs stays out of the repository.
* 2026-11-06: `night.sh` has no fixed time; the lead starts it when
  planned, with no fallback run.
* 2026-11-13: up to six heavy runs at once on F53, a timing run alone.
* 2026-11-18 (006-30, decision 3): only the lead pushes `main`, after the
  privacy check.
* 2026-11-19 (028-23, 028-27): functional tests in `before-commit.sh`,
  `night.sh` and `week.sh`, timing in `timing.sh`, the only one that needs
  a quiet machine; the three are disjoint, and all run before every
  release on a commit near it.
* 2026-11-23: the coordinator is renamed the lead (013-04); the
  requirements of section 1; no modes, three classes, 07:00 on weekdays,
  no phone notifications; the model and effort of section 9. These
  replace the effort rules of 2026-10-28 to 2026-11-11 (013-02,
  section 9).
* 2026-11-23: the ten choices of plan section 13, all as recommended: the
  class lists; a push is class 1; class 2 at least 30 minutes ahead; a
  Fable agent is class 2; the limit back to 50 % at the week's reset; the
  check-in every 30 minutes (hourly if an idle one costs over a tenth of a
  point); four agents, two at `tight`; 013-01 marked done; a dead session
  accepted, with `news.md` and `/lead` in the morning; no agents during a
  timing run.
* 2026-11-23: no separate rehearsal; the first night is the test
  (section 10).
* 2026-11-23, decided in the scripts by the implementation, where the
  plan left it open: `PAUSE` after a gap of more than 45 minutes;
  `SUMMARY DUE` only for a lead that ran before its hour that day; the
  marker `summary-YYYY-MM-DD` and `summary-time`; a `pending` line is
  `YYYY-MM-DD HH:MM NAME: DEFAULT`; the watchdog writes `news.md` only for
  a dead or silent lead (at the limit the lead writes it), removes only a
  `STOP` it wrote, ends at `closed` or with the session's process, and
  starts no second one for the same state directory; `status.sh` also
  prints `PERMISSION MODE`.
* 2026-11-23, decided in the skill: the check-in at minutes 13 and 43 of
  every hour, prompt "Lead check-in: do the lead skill's wake-up (load the
  skill if needed)."; the marker `closing`; the state template in lists,
  not tables.

**The fresh-agent test** (plan section 12, step 5; 2026-11-23). A new
subagent (Opus, effort high) read only `SKILL.md` and the three scripts'
headers and said what the lead does on each of the seven lines in capitals
and which class each of twenty sample decisions has. All seven and all
twenty were right: eight of class 1 (028-41 next when the plan has run
out; `night.sh` at 23:00; a Lean proof on Opus xhigh; a gated fix of a
flaky test pushed; a new 028 entry for a finding; deleting its own clones;
an agent restarted with a sharper brief; a Codex review), five of class 2
(a Fable agent for a large plan; a 40-second step added to
`before-commit.sh`; the check-in hourly; renaming an internal package
unasked; the Android tests moved to `night.sh`), six of class 3 (the tag;
a field in the stream format's meta block; a public method; an item done;
the limit raised; deleting Frans's old bench directory), and a tag that
Frans had allowed for the night, decided by the lead. Six of its ten notes
on unclear text were fixed in the skill: the wording of a day's authority;
what "own run data" is; a push is class 1 though it cannot be undone (the
class 3 item is "any other decision"); `DUE` goes ahead within the level;
the tasks stopped by `STOP` restart from their State notes; the agent's
"output file". The other four needed no change: a gate step that adds 40
seconds is not "a fix of a harness" (the agent read it so); a change of
the check-in or an unasked cleanup is class 2 by the letter, and the agent
also weighed "invent no new direction", as intended; the plan's place is
section 8 here.

A second new agent, with the same twenty decisions and two more lines
(`STOP` and `PAUSE` in one output; `DUE ?`), read the skill after the
first review by Codex (below). All nine and all twenty were right: it
resumed nothing while `STOP` stood. On its notes, two lines were made
clearer: tasks restart once `STOP` has gone, and a `DUE ?` line is mended
from the plan.


**The review by Codex** (plan section 12, step 6; 2026-11-23): GPT-6.1-Sol,
reasoning effort high, in a clone of its own, as in section 9; the prompt
asked for every point where the skill or this description leaves out or
contradicts the plan, or does not match the scripts. It found six, all
fixed:

1. `STOP` and `PAUSE` together: the skill said to resume stopped agents,
   which would override `STOP`. Now `STOP` means start and resume nothing
   on Claude, whatever the other lines say (section 3).
2. `DUE ?`, a line of `pending` that does not parse, would have been
   followed as a default. Now the lead mends the line (section 3).
3. The watchdog's report of a dead session could wait for `usage.sh`,
   whose call to `claude` had no time limit. Now `usage.sh` stops a
   `/usage` that takes over a minute (`USAGE_TIMEOUT`), which counts as
   not read, and the watchdog reads no usage once the process is gone; two
   checks in `test/run.sh` show both (sections 10 and 11).
4. The plan's renewal of the check-in job every five days had been
   dropped, as the job expires after 30 days. It is kept, as the plan says
   (section 5; the skill).
5. Two of 013-01's sections of a plan were missing: the principles each
   task must keep, and what happens if the session stops (section 8).
6. The path of the implementation's clone in the State note: removed
   (AGENTS.md, "Public repository").

Its own run of `test/run.sh` failed in its sandbox, which denies `ps`; the
tests pass outside it (`LEAD TESTS OK`).

A second review by Codex, of the fixed version (the same prompt, with
the first review's points to check), found the six fixed but for a part
of the third, and five more. Four were fixed, one is answered:

1. The repair could start agents without reading `status.sh`, so also
   under `STOP`. Now it runs `STATUS` first and starts agents as its
   lines allow (the skill; section 5).
2. The repair after a restart could be left without a watchdog: the new
   one exited while the old one, for the dead process, still ran its
   last round. Now a watchdog for another process of the same lead stops
   the old one and takes over; a check in `test/run.sh` (section 10).
3. A `/usage` that printed its report and then hung was read after the
   timeout. Now a timed-out call counts as not read whatever it printed;
   a check in `test/run.sh`.
4. The example status line said `ok` at 43 % with a limit of 50 %,
   which is `tight`: now 33 %, here and in the scripts' headers (the
   plan, section 2, has the same slip).
5. Answered: `SUMMARY DUE` only for a lead that ran before its hour that
   day, which the plan does not say (plan section 4: from 06:00 until the
   marker). Kept: the summary reports the night, and a lead started after
   06:00 had none; Frans started it and is there. A lead that runs over
   several days, or one repaired after a restart, keeps its `status.log`
   and gets the line. Decided in the scripts (above).

A third review by Codex found the ten fixes in place and two points:

1. Again the `SUMMARY DUE` of a lead that ran before its hour, as a
   change of the plan that Frans has not approved. Read literally, plan
   section 4 makes `status.sh` print `SUMMARY DUE` from 06:00 until the
   marker for any lead, so a lead started at 10:00 would be told at once
   to write the 07:00 summary. The condition stays, and it goes to Frans
   as a class 2 decision ("kept unless Frans says otherwise") at the
   landing (plan section 12, step 8).
2. An agent that ended on an error in an outage shorter than 45 minutes
   got no `PAUSE` and was resumed only by the 30-minute rule for a
   stalled agent. Now every wake-up resumes an agent that ended on an
   error, unless `STOP` holds (the skill; sections 6, 9 and 10).

A fourth review by Codex found the eleven fixes in place, the
`SUMMARY DUE` point again, and one more: the resume of every agent that
ended on an error also covered agents that cannot authenticate, which
are resumed only once a test agent works. Fixed in the skill: "resume
none" for a 403, and the resume on an error points to it (section 9).
The `SUMMARY DUE` point stays open until Frans decides it.

A fifth review by Codex found two more, both fixed: `PAUSE` in the skill
still said to resume stopped agents without the exception for a failed
authentication (now it points to the common rule); and the first night's
network gap of 20 minutes gives `PAUSE` only when it spans a check-in, so
that the gap in `status.log` passes 45 minutes (section 10).

A sixth review by Codex found two more, both fixed: the watchdog read the
usage every other round, so that with the time of its calls `STOP` could
come later than ten minutes after the limit; it now reads it every round
(section 6). And 013-01's rule that the lead takes no work another
session owns was missing when the plan runs out (section 5; the skill).

A seventh review by Codex found the sixteen fixes in place and one more
point, fixed: this description said that a `DUE` waits under `STOP`,
where only what needs Claude waits; a default carried out by a run or by
Codex goes ahead (section 3). With that, every point of the seven
reviews is fixed but `SUMMARY DUE`, which waits for Frans.

## 13. Lessons

* **Mechanism belongs in scripts.** A procedure the model carries out at
  every check-in grows and drifts; a script's line in capitals is the same
  at every wake-up (the coordinator, 2026-10-28 to 2026-11-22).
* **State files that grow are read again and again**: November's state
  files reached 600 lines. Keep only what is live; the record is the plan.
* **A smoke test must check the output, not only the exit code** (006-09:
  a step exited 1 at night because its output was not parsed).
* **An API question found at night** becomes a decision entry (a 028 entry
  of kind decide) and the test is fixed at once, instead of the lead
  deciding it (006-09).
* **A subagent's Write may be refused** for a file. It then returns the
  text in its report, and the lead saves it.
* **The Git index is shared.** A deletion staged by one session could have
  gone into another session's commit: stage right before committing, and
  commit with a path list (006-09).
* **Times from `date`.** 006-09 had to correct several progress lines
  written with expected times.
* **A watch on the usage by hand** was written by the coordinators on
  several days (006-32); the watchdog's `STOP` replaces it.


## 14. Files

* [04-lead/skill/](04-lead/skill/), the Claude Code skill `lead`:
  * [SKILL.md](04-lead/skill/SKILL.md): what the lead is, `/lead` (start
    or repair), the wake-up, the decision classes, the cycle, subagents,
    runs and Codex, landing, closing;
  * [state-template.md](04-lead/skill/state-template.md), the template of
    `state.md`;
  * [usage.sh](04-lead/skill/usage.sh), the usage, the weekly limit and
    the level;
  * [status.sh](04-lead/skill/status.sh), the status line and the lines in
    capitals;
  * [watchdog.sh](04-lead/skill/watchdog.sh), the watchdog;
  * [test/run.sh](04-lead/skill/test/run.sh), the scripts' tests on canned
    inputs, with a live `/usage` report of 2026-11-23.
* [04-lead/plan.md](04-lead/plan.md), the plan for the cleanup of the
  skill, with Frans's choices of 2026-11-23.

Installed by a link:

    ln -s /Users/f/fl/repos/bergdb/items/013-ai-work/04-lead/skill ~/.claude/skills/lead


## State of the implementation

2026-11-23, the cleanup of plan.md, in a clone of `main` made for it
(base 004382f9); landed in `main` on 2026-11-24 in one commit, between
leads (plan section 12, step 8).

* Steps 2 to 4 of plan section 12 are done in commit 19ef14e2: `usage.sh`
  (the limit file and `-L N`, every row of the report, the levels ok,
  tight and stop), the new `status.sh`, and `watchdog.sh` for the lead's
  whole life. `sh skill/test/run.sh` prints `LEAD TESTS OK` (about a
  minute; stand-ins only, no model call). A live reading on 2026-11-23 at
  22:28 gave the same figures as the screen of `claude -p /usage`.
* Step 5: `SKILL.md` in 120 lines and the state template in 20, by plan
  section 8; the fresh-agent test passed (section 12).
* Step 6: this description rewritten, so that a lead needs nothing from
  013-01 or 013-02. Seven reviews by Codex found eighteen points;
  seventeen are fixed, and one waits for Frans as a class 2 decision: `SUMMARY
  DUE` only for a lead that ran before its hour (section 12). Among the
  fixes, in the scripts: a time limit on `/usage`, and a watchdog for a
  restarted session that replaces the old one. `test/run.sh`: 101
  checks, `LEAD TESTS OK`.
* Step 7: replaced by the first night, step 9 (Frans, 2026-11-23).
* Step 8, 2026-11-24: landed in one commit after lead-1123, the last lead
  on the old skill, had closed and with no watchdog running; `LEAD TESTS
  OK` on the main tree; 013's readme and log; 013-01 marked done (choice
  8). Frans chose to land without a separate review and to test the skill
  in use: lead-1124, started that morning on the old skill, moved to the
  new one (`/lead`'s repair).
* Next: step 9, the first real night on the new skill. Open for Frans:
  `SUMMARY DUE` only for a lead that ran before its hour (section 12),
  kept unless Frans says otherwise.
