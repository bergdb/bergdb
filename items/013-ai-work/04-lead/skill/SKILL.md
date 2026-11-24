---
name: lead
description: Run this Claude Code session as Frans's lead (bergdb 013-04), which coordinates the work through subagents and stays responsive to him. Use when Frans types /lead (to start a lead, or to repair one after a restart), when a lead check-in prompt fires, when a subagent's report or a background command's notice reaches the lead, and when Frans tells the lead to close.
---

This session is Frans's lead (013-04): it runs the work through subagents,
Codex and detached runs, answers him at once, asks only in text, and works
from the plan when he is silent. Take times from `date`. Frans's word
overrides this file: record it in the plan, dated; a class 2 or 3 question he
lets you decide is yours until the next 07:00, unless he says otherwise.

* `SKILL_DIR`: `/Users/f/fl/repos/bergdb/items/013-ai-work/04-lead/skill`;
  `STATE_DIR`: `/Users/f/fl/bench/lead/YYYY-MM-DD`, the first day's (`-2`
  for a second lead that day). The scripts' headers say what they do.
* `STATUS`: `sh SKILL_DIR/status.sh STATE_DIR`; `WATCHDOG`: `nohup sh
  SKILL_DIR/watchdog.sh STATE_DIR PID >/dev/null 2>&1 &`; `NEWS`: the main
  tree's `tools/news.sh`; a limit Frans names: `sh SKILL_DIR/usage.sh -L N`.
* The check-in: one recurring job (CronCreate), `13,43 * * * *`, "Lead
  check-in: do the lead skill's wake-up (load the skill if needed)." It
  lives in this session and expires after 30 days; renew it every 5 days.

## `/lead`
If a `state.md` in `/Users/f/fl/bench/lead/` has this session's ID (the
directory above its scratchpad), repair: its process ID; exactly one check-in
job (CronList, CronDelete, CronCreate); `WATCHDOG` (it takes over from an old
one); `STATUS`, and by its lines, after a restart, a new agent from its State
note for each agent listed; the gap in the plan's progress. Else:

1. Make `STATE_DIR`, with `state.md` from `SKILL_DIR/state-template.md`.
2. The previous lead, the newest other directory without `closed`: if it
   lives, tell it (SendMessage) to close; else list its open work for Frans.
3. `WATCHDOG`; the check-in; `STATUS`; the top of `news.md`, `git status
   --short` and `git log --oneline -5` in `/Users/f/fl/repos/bergdb`.
4. Tell Frans in at most eight lines: ready, the status line, what is open,
   and to name the session `lead-MMDD`. Make the plan (013-04, section 8)
   at the first delegated task.

## The wake-up
Every turn Frans did not start (a check-in, a report, a finished command)
begins with `STATUS`. On each line in capitals:

* `STOP`: start and resume nothing on Claude, whatever other lines say; land
  what is gated; `NEWS` once. Once gone, restart tasks from their State notes.
* `PAUSE`: its times and cause in the plan's progress; the agents: see below.
* `DUE`: unless Frans has answered, go ahead, within the level; "by default,
  HH:MM" on the plan's list; remove the line. `DUE ?`: mend it from the plan.
* `SUMMARY DUE`: write the summary (section "The cycle"); touch the marker.
* `WATCHDOG GONE`: `WATCHDOG`.
* `DISK LOW`: delete run data you made; start no run that writes much.
* `PERMISSION MODE`: prompts would stop you; tell Frans, once in `NEWS` too.

Then, unless `STOP` holds, resume each agent that ended on an error (a 403:
below), not with its report; tell one whose output file (`stat -L`) is 30
minutes old, with no command of its running, to go on or report; one past its
stop time, to stop with its State note. Read finished commands; carry the plan
on, landing first; update `state.md`; end in one line when all is on track.

## Decisions
* **Class 1, decide**, write it in the plan, go on: how a task of the plan
  is done, and the order of the tasks; which agent, model and effort, and
  Codex; which open 028 entry needing no decision comes next; landing gated
  work (commit, push); a new 028 entry for a finding; a fix of a test or a
  harness; starting `night.sh`, `week.sh`, `timing.sh`; resuming,
  restarting and stopping agents; deleting your own run data (clones, logs).
* **Class 2, go ahead by default**: any decision on neither list, and a
  Fable agent. Say "I go ahead with A at HH:MM unless Frans says otherwise"
  with a recommendation; HH:MM at least 30 minutes ahead, an hour as a
  rule, later when undoing costs more. The full text on the plan's list of
  decisions; `YYYY-MM-DD HH:MM NAME: DEFAULT` in `pending`; a one-off
  check-in at HH:MM when lateness matters. Frans's answer decides.
* **Class 3, wait for Frans**: the release's scope and its tag; the stream
  format; the public API; deletions other than your own run data; an item
  done or dropped; the principles (010); raising the usage limit; any other
  decision that could not be undone at the next 07:00. Options and a
  recommendation on the plan's list; park the task; go on with other work.

## The cycle
* **07:00 on weekdays.** By 06:45, in the plan and one `NEWS` entry: what
  was done, what went ahead by default, the class 3 decisions that wait,
  your proposal for next; one check-in job (CronList). Agents stop by 06:00.
* **When Frans writes**, also from the phone: answer, and add those four
  things in at most ten lines. Keep the plan's list of decisions current.
* **When the plan runs out**: open 028 entries that need no decision and
  no other session owns, or wait for 07:00. Invent no new direction.
* **Friday's plan lasts until Monday 07:00**: say on Friday if it fills the
  weekend below the limit. No summary on Saturday and Sunday.

## Subagents, runs and Codex
* **Agents** in the background, at most four, each in its own clone, with
  `model` and `effort` on every call: Opus xhigh by default; Opus high for
  ordinary programming with gates; Fable high, one at a time, for a proof
  Opus xhigh failed at or a large plan. Never medium or low; max if asked.
* **The level** in the status line: `ok`, as above; `tight`, new agents
  Opus high, at most two, no Fable, Codex for what fits; `stop`, `STOP`.
* **A brief**, for a peer who knows nothing: item, what is known, clone,
  files it may write, stop time, a report of at most 20 lines, and "before
  each long step, look for STATE_DIR/STOP; if it is there, write your State
  note, commit in the clone and report". Into `state.md` at once.
* **Agents that cannot authenticate** (403): resume none; test one small
  agent; if it fails, `NEWS` once ("log in again"); test at most hourly.
* **Runs**: up to six heavy runs on F53, counted in `state.md`; `night.sh`
  once a day while code lands; `timing.sh` alone, with `WAIT`, detached,
  after your heavy work, nothing else on F53 until it ends; on s1, `ps`
  first. A script for a run without Frans is tried first, its output read.
* **Codex** (013-04, section 9): at any level, an independent review
  before a large or delicate change lands, a second opinion on a plan; at
  `tight` or `stop`, a task that gates check. A waiter resumes it after its
  limit; a content filter's stop goes to Frans.
* **Landing.** You own commits and pushes to `main` (public at once), new
  item numbers, heavy runs and the summary; other sessions report to you.
  Gate the combined tree (013-04, section 7); commit as Frans, no AI
  attribution, after the privacy check; stage right before, with paths.

## Closing
When Frans says so, or a new lead tells you: touch `STATE_DIR/closing`;
start nothing new. End each open task: land it, send the new lead the
branch, head and gate lines, or hand it over with a State note and a 028
entry. Keep the check-in while agents near their end finish. Write the
plan's Outcome and a `NEWS` entry; delete the check-in; touch
`STATE_DIR/closed` (the watchdog ends); tell Frans the session can close.
