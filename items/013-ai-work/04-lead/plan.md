# 013-04 plan: the cleanup of the lead skill

Created 2026-11-23 by Claude (Fable 5.2, Claude Code), at Frans's request.
Revised 2026-11-23 after Frans's decision on modes (section 1).
Status: open; a plan, not implemented. Frans chose all ten
recommendations of section 13 (2026-11-23).

The lead skill is a copy of the coordinator's (013-02), which grew from a
quick test to 349 lines. This plan says what the skill becomes, how it is
tested and in which order the work is done. Section 13 collects the
choices that are Frans's; the rest assumes the recommendations. Facts
about Claude Code were checked on 2026-11-23 on F53 (versions 2.1.317 to
2.1.330) unless marked "not tested".


## 1. The requirements

Frans, 2026-11-23:

* The lead coordinates the work through subagents and stays responsive
  for Frans. Often it starts in the morning and runs until 07:00 the next
  morning; it may run several days when Frans says so.
* The skill is as short as possible. What matters most is that the lead
  works when Frans is at neither the computer nor the phone.
* The lead consumes at most 50 % of the week's usage; Frans will change
  the number during the week.
* The lead session typically runs Opus xhigh, set by Frans. Subagents
  run Opus xhigh (the default), Opus high (ordinary programming, simpler
  tasks, near the limit) or Fable high (hard proofs, planning).
* Codex is a kind of subagent: second opinions, reviews, and when
  Claude's usage is tight.
* Frans can override any of this. The skill may name him.

Frans, 2026-11-23, 08:25, in place of attended and unattended modes:

* **No modes.** When Frans writes, the lead answers and plans with him;
  when he does not, it works from the plans in the documents. The lead
  never needs to know which, so nothing detects his presence.
* **One rule for decisions**, in three classes, the same whether he is
  there or not (section 3).
* **07:00 on weekdays** is the fixed point to stop and consolidate
  (section 4).
* **No phone notifications** for now.


## 2. The design in brief

The coordinator skill is long because the model carries the mechanism:
it switches modes by procedure, starts and stops the watchdog, replaces
check-in jobs, compares heartbeat times, reads usage levels from a table.
The cleanup moves the mechanism into scripts and leaves rules:

* **`status.sh`** (new) is the first call of every turn that Frans did
  not start: a check-in, an agent's report, a finished command. It prints
  one line (wrapped here), and a line in capitals for each thing due:

      2026-11-24 22:37 Tue; week 43 %, limit 50 %: ok; watchdog up;
      disk 212 GB; next summary Wed 07:00

  The lines in capitals: `DUE` (a class 2 deadline has passed), `STOP`,
  `SUMMARY DUE`, `WATCHDOG GONE`, `PAUSE` (with its times), `DISK LOW`.
  It computes no mode. Its output goes to `status.log`, whose age is the
  heartbeat.
* **`watchdog.sh`** (extended) runs outside the session for the lead's
  whole life: it keeps the Mac awake, writes `news.md` when the lead is
  dead or silent, and writes the `STOP` file at the limit.
* **`usage.sh`** (changed a little) reads the usage and the limit file.
* **One check-in**, every 30 minutes, with one prompt.
* **`SKILL.md`**, about 100 lines: three procedures (start, wake-up,
  close), the decision classes and the rules.

Considered and dropped: a rule that the lead goes unattended after 90
minutes without human input. It can be computed (Claude Code's
transcript marks each prompt's origin: `turnOrigin` is `human`, also from
the phone, against `scheduled`, `task_notification` and `peer`), but
after Frans's decision no rule depends on his presence.


## 3. Decisions: three classes

Classes 1 and 3 are lists in the skill, not judgment. A decision on
neither list is class 2.

**Class 1: the lead decides**, writes it in the plan and goes on:

* how a task of the plan is implemented, and the order of its tasks;
* which agent, with which model and effort (section 7), and Codex;
* which open 028 entry comes next, among those that need no decision;
* landing gated work: commit and push after the gates and the privacy
  check;
* a new 028 entry for a finding; a fix of a test or a harness;
* starting `night.sh`, `week.sh` and `timing.sh`;
* resuming, restarting and stopping agents; deleting its own run data.

**Class 2: goes ahead by default.** The lead states it in the chat with
a recommendation: "I go ahead with A at HH:MM unless Frans says
otherwise". It picks the time to fit the decision: at least 30 minutes
ahead, an hour as a rule, longer when undoing costs more. The mechanism:

* The lead adds a line to `pending` in the state directory: the time, a
  short name, the default. The plan's list of decisions has the full
  text.
* `status.sh` prints `DUE` for each line whose time has passed. The
  30-minute check-in meets the deadline: the decision goes ahead at the
  first wake-up after HH:MM, up to half an hour late, never early. When
  lateness matters, the lead also sets a one-off check-in at HH:MM.
* On `DUE` the lead checks that Frans has not answered, goes ahead,
  records it in the plan as "by default" with the time, and removes the
  line. If Frans answers first, his answer decides and the line goes.
* What went ahead by default can be undone by Frans at the next 07:00;
  a decision that could not be undone then is class 3.

**Class 3: waits for Frans.** The release's scope and its tag; the
stream format; the public API; deletions (not the lead's own run data);
an item done or dropped; the principles (010); raising the usage limit.
The lead writes the options and a recommendation on the plan's list,
parks the task, and goes on with other work.

**Wider authority for a day.** Frans may say that the lead decides
something of class 2 or 3 tonight. The lead records it in the day's plan
as a dated decision; it ends at the next 07:00 unless he says otherwise.


## 4. The cycle

* **07:00 on weekdays.** By 06:45 the lead has written, in the plan and
  as one `news.md` entry that points to it: what was done; what went
  ahead by default; the class 3 decisions that wait; its proposal for
  where to go next. `status.sh` prints `SUMMARY DUE` from 06:00 until the
  lead touches the day's marker. Agents get stop times of 06:00, so that
  Frans meets landed work and a clean main tree.
* **Mornings** are planning together: Frans settles the decisions and
  the next plan.
* **When Frans writes at another time**, also from the phone, the lead
  answers and adds the same four things in short form, at most ten
  lines. The plan's list of decisions is updated when a decision is
  stated, goes ahead or is settled, so it is current at any hour.
* **When the agreed plan runs out**, the lead takes open 028 entries that
  need no decision, or stops and waits for 07:00. It invents no new
  direction.
* **Friday's plan lasts until Monday 07:00.** At Friday's planning the
  lead says whether the plan's work and the room below the limit cover
  the weekend, and proposes more if not. No summary on Saturday and
  Sunday; a failure reaches `news.md` when it happens.


## 5. What is left of 013-01's night machinery

Not used by the lead any more: the conductor with `steps.txt`, the READY
and DONE markers and its quiet check (`timing.sh` refuses or waits for a
busy machine itself, 028-23; 006-32's release runs needed no conductor);
the stop of all CPU work at 21:45 and the idle session at night; the
check-in ladder of 05:57 to 06:44 (`SUMMARY DUE` replaces it); the
conductor's fallback news at 06:50 (the watchdog reports a dead or
silent lead when it happens).

Kept, as rules of the skill:

* **A timing run.** The lead starts `java/timing.sh` with `WAIT` as a
  detached command when its own heavy work has ended. Until it ends, the
  lead starts no agent and no other run on F53. On s1 it checks `ps`
  first.
* **Heavy runs.** Up to six at once on F53, a timing run alone (Frans,
  2026-11-13). The lead counts them in its state file; other sessions
  ask it.
* **Smoke tests.** A script made for a run without Frans is tried first,
  and its output is checked, not only its exit code.

013-01's rules that still hold (clones, gates, commits, the plan's
sections) move into 013-04's description; 013-01 becomes the record of
the first nights and the home of the conductor.


## 6. The weekly limit and usage

**What it counts.** The row `weekly_all` of Claude Code's `/usage`: the
account's week over all models, from every session and machine, Frans's
own sessions included. Codex has its own quota. The limit is a ceiling
on that figure, not a budget of the lead's own. A second row,
`weekly_scoped`, is printed; what it scopes is found out in step 2.

**Where it is stored.** One file for all leads,
`/Users/f/fl/bench/lead/limit`: the percent, the reset time of the week
it was set in, and when Frans set it. Only Frans raises it (class 3).
When he names a number, the lead runs `usage.sh -L N` and answers with
the status line, which shows the limit. `usage.sh` reads the file on
every call, so every check-in, every new lead and the watchdog see the
latest value. Missing, or from an earlier week: 50 %.

**The levels** replace plenty, normal, tight and limit:

* `ok`: more than 10 points below the limit.
* `tight`: within 10 points. New agents run Opus high, at most two at a
  time; landing comes before starting; a task that fits Codex goes
  there.
* `stop`: at or above the limit. Nothing new starts on Claude; running
  agents stop at their next step. The lead lands what is gated, writes
  `news.md` once, and goes on only with the runs and Codex.

**The stop does not depend on the model.** Every ten minutes the
watchdog reads the usage (`usage.sh` calls no model) and, at `stop`,
writes `STOP` in the state directory. It removes the file when the limit
is raised or the week resets. Each agent's brief says: look for `STOP`
before every long step; if it is there, write the State note, commit in
the clone and report. The week may pass the limit by a point or two.
The coordinators wrote such a watch by hand on several days (006-32).
An hour of unreadable usage also gives `STOP`, until it reads again.

**The account's own limit** (the week at 100 %, an error 429): every
call fails until the reset; the first check-in after it prints `PAUSE`,
and the lead resumes its agents. **The 5-hour window** has not been in
`/usage`'s report since 2026-11-08; the lead does not pace by it.
**What 50 % buys:** an agent has cost roughly one point of the week per
hour in November, so three agents reach the limit within a day and a
night.

**Codex** is used at any level for an independent review of a large or
delicate change before it lands and for a second opinion on a plan, and
at `tight` and `stop` for tasks with a clear "done when" that gates
check. It runs detached (`codex exec`, 020-14, section 1) in a clone of
its own, from a prompt file, with a report file. Its sandbox cannot
commit: the lead reads the report, gates and commits. When Codex stops
on its own limit, the lead starts a waiter that resumes it at the retry
time. When a content filter stops it, the task is not reworded; it goes
on the list for Frans.


## 7. Model and effort for subagents

The lead passes `model` and `effort` on every Agent call.

* **Opus xhigh**, the default: proofs, concurrent code, design, reviews,
  investigations.
* **Opus high**: ordinary programming with a clear "done when" and gates
  that catch mistakes, and every new agent at `tight`.
* **Fable high**: a proof that Opus xhigh failed at, or the plan of
  large work. One at a time, none at `tight`, and class 2: stated with
  a time before it starts.
* Never medium or low; max only when Frans asks.
* At most four agents at a time, two at `tight`.
* The lead session's own model and effort are Frans's to set.


## 8. The skill after the cleanup

**Target.** `SKILL.md` about 100 lines (349 now), at most 120. The state
template at most 20 lines (41 now).

**What it holds:** what the lead is (6 lines); files and paths (8);
`/lead`: start, or repair (12); the wake-up: run `status.sh`, do what it
prints, look at the agents and commands, end in one line when all is on
track (14); the three classes with their lists (22); the cycle (10);
subagents, runs and Codex (18); landing and the shared things (8);
closing (8); Frans's word overrides, recorded in the plan as a dated
decision (2).

**Removed:** the sub-commands `attended`, `unattended`, `closing`,
`check-in` and `resume` with their procedures and the round of dialog
questions; the switching of check-in jobs and of the watchdog; the quiet
block and the night hours; the section "Effort" (40 lines); the section
"Usage" and its table; the watchdog's description (in its header); the
pause arithmetic (`status.sh` prints `PAUSE`); the story of 2026-11-13's
failed authentication (two lines stay); rules stated twice; "heavy runs,
one at a time" and "019".

**The state directory**, one per lead, holds `state.md` with only what
is live (the plan's ID, the running agents with task, clone, model,
output file and stop time, the background commands, what comes next),
`pending`, `status.log`, `STOP` and the watchdog's files. The mode, the
usage and the events leave `state.md`: `status.log` and the plan's
progress have them. November's state files grew to 600 lines that every
check-in read again.

**What moves to 013-04's description:** the reasons; the roles; the
status line; the levels; section 9's list with the test results; the
Codex command; the Claude Code facts the scripts rest on; the dated
decisions; the lessons.


## 9. Robustness without Frans

### 9.1 What can stop or stall the lead

1. **A permission prompt or a dialog question** stops the session. It
   runs in auto mode, and `status.sh` prints a line when the transcript
   shows another mode; a refusal by auto mode is final, with no
   rewording. The lead asks only in text. Seen to work nightly; the
   check is new.
2. **A decision nobody answers.** Section 3: class 2 goes ahead on
   `DUE`, class 3 is parked. New.
3. **Frans's limit.** Section 6: `STOP`. By hand so far; new as part of
   the watchdog.
4. **The account's limit, errors 429 and 529, the network.** The first
   check-in after it resumes the agents. Seen to work since 006-09;
   outages were rare and minutes long in fifteen watchdog logs, and a
   long one is not tested.
5. **Agents cannot authenticate** (2026-11-13). The lead tests with one
   small agent, writes `news.md` once, and tests again once an hour.
   Cannot be provoked: accepted as untested.
6. **The session is dead.** Its check-ins and agents are gone; detached
   runs go on. The watchdog writes `news.md` within ten minutes; Frans
   reopens the session and types `/lead`. Not seen by the watchdog in
   fifteen logs. A restart of the Mac kills the watchdog too: the
   missing summary is then the only sign.
7. **The lead does not wake**: its check-in job is gone (they expire
   after seven days), or a turn hangs. The watchdog writes `news.md`
   when `status.log` is 75 minutes old while the process lives; the lead
   keeps exactly one job, checked at every summary. New.
8. **The Mac sleeps, or the watchdog is gone.** The watchdog runs under
   `caffeinate -i` (no gap over six minutes in fifteen logs; a closed
   lid still sleeps) and logs a gap in its own rounds. `status.sh`
   prints `WATCHDOG GONE`, and the lead starts it again. New.
9. **An agent stalls.** One listed as running whose output file has not
   changed for 30 minutes, with no command running, is told to continue
   or report; past its stop time, to write its State note and stop.
   Seen to work.
10. **The disk fills.** `DISK LOW` under 40 GB: the lead deletes run
    data it made and starts no run that writes much. New.
11. **The context is compacted.** What another session needs is in the
    state file or the plan before a turn ends. Seen to work (006-32).

### 9.2 The rehearsal

Replaced by the first night (Frans, 2026-11-23): no separate rehearsal
on an afternoon. The first night with the new skill does real work and
is the test; at night, when it disturbs no one, the lead stages the
network gap (step 6) and the killed watchdog (step 7); `STOP` and the
other staged steps are covered by the scripts' tests (section 12, steps
2 to 4) and by what the night brings. The audit below applies to that
night. The rehearsal as planned:

About three hours on an afternoon, on the new skill, with two small real
tasks (028 entries, Opus high). The lead stages all but Frans's four
actions. For the test, the limit is the week's figure plus two points
and the summary's time is two hours ahead (a file in the state
directory). What is expected:

1. **Frans** types `/lead` and names the tasks: a status line every 30
   minutes.
2. A class 2 decision planted in one brief, 30 minutes ahead: stated in
   the chat, a line in `pending`, `DUE` at the first check-in after the
   time, "by default" in the plan.
3. A class 3 decision planted in the other brief: parked on the plan's
   list with a recommendation, while the first task goes on.
4. The limit is reached: `STOP` within ten minutes, the agents' reports
   with State notes within fifteen, one `news.md` entry.
5. **Frans** asks from the phone how it stands and names a higher limit:
   the four things in short form, the limit in the status line, `STOP`
   gone within ten minutes, the agents resumed.
6. Wi-Fi off for 20 minutes, by a detached script: `PAUSE` with "network
   down", a line in the progress, the agents resumed.
7. The watchdog killed: `WATCHDOG GONE`, and a new one.
8. The summary's time: `SUMMARY DUE` an hour before, the plan's four
   parts and the `news.md` entry 15 minutes before.
9. **Frans** quits VS Code: the watchdog's `news.md` entry within ten
   minutes. He reopens the session and types `/lead`: one check-in job,
   a watchdog, the agents started again from their State notes.
10. **Frans** writes "close": section 10's closing.

`status.log` is the audit: a line at least every 35 minutes outside
steps 6 and 9. The first real night is the second test, with the same
audit and the cost of an idle check-in in its summary. Not provoked:
failed authentication, a closed lid, the account's limit.


## 10. Closing, and leads of several days

**A lead runs until Frans closes it**, not until 07:00. After a
morning's planning he goes on with the same lead or starts a new one.

**Closing** starts when Frans says so, or when a new lead starts and
tells the old one. The lead touches `closing` and then:

1. starts nothing new;
2. ends each open task: it lands it, or, when a new lead has started,
   sends that lead the branch, the head and the gate lines; or it hands
   the task over with a State note and a 028 entry;
3. keeps agents that are near their end until they report (agents cannot
   move to another session), with its check-in;
4. writes the plan's Outcome and a `news.md` entry;
5. deletes its check-in, ends the watchdog, touches `closed`, and tells
   Frans that the session can be closed.

**`/lead` in a session that has a state directory** repairs instead of
starting: the process ID, exactly one check-in job, the watchdog, and a
new agent from the State note for each agent listed but gone.

**Several days** differ in little, since the cycle is the same every
day: one plan for the lead's life, with the progress under dated
headings; `night.sh` once a day while code lands; the check-in job made
again when it is older than five days; at the week's reset the limit is
50 % again and the watchdog removes `STOP`.


## 11. The cut-over from /coordinator

On 2026-11-23 both links exist in `~/.claude/skills/`, so every session
lists two skills with the same triggers; the last coordinator closed on
2026-11-22.

1. **Remove the link `~/.claude/skills/coordinator`** at once, after a
   look at `~/.claude/sessions/` that no coordinator session is open.
   013-02's skill directory stays in the repository as the record.
2. **The names in the maintained files**, one commit: AGENTS.md, line
   97, and the comments of `java/night.sh`, lines 5 and 6, and
   `java/week.sh`, line 5: "the day's coordinator (013-02)" becomes "the
   lead (013-04)". The scripts are edited only while neither runs, and
   `java/before-commit.sh` prints `BEFORE COMMIT OK` before the commit.
3. **Not changed**, as history: `docs/log.md`, the day plans, 013-02,
   016-01, a Java comment of 2026-11-09.
4. **The cleanup** lands later, in one commit: the scripts, `SKILL.md`,
   the template and 013-04's rewritten description. It lands between
   leads, when no watchdog runs from the main tree. Until then 013-04
   points to 013-02 for the mechanism.

Steps 1 to 3 are the rename and do not wait for step 4.


## 12. The steps

In a clone; an agent on Opus high for steps 2 to 4, Opus xhigh for 5 and
6. Each is done when:

1. **Frans's choices** (section 13): each has a dated line here. Done
   2026-11-23: all ten as recommended.
2. **`usage.sh`** (the limit file and `-L`, every row, three levels):
   canned reports give the expected line (below, within 10 points, at
   the limit, a limit of an earlier week, no rows), a live reading
   equals the `/usage` screen, and `weekly_scoped` is explained.
3. **`status.sh`**: canned files give each line in capitals once and at
   the right time, among them `DUE` from `pending` and `SUMMARY DUE` on
   a weekday but not on a Saturday.
4. **`watchdog.sh`** (the lead's whole life, `STOP` written and removed,
   the silent lead, its own gaps): stand-ins for the process, the usage
   and `tools/news.sh` show each event reported once.
5. **`SKILL.md` and the template** (section 8): at most 120 lines, and a
   fresh agent that reads only it and the scripts' headers says
   correctly what the lead does on each line in capitals and which class
   each of twenty sample decisions has.
6. **013-04's description**: a lead needs nothing from 013-01 or 013-02,
   and a review by Codex of description and skill against this plan has
   no open finding.
7. **The rehearsal**: replaced by the first night, step 9 (Frans,
   2026-11-23; section 9.2). As planned: (section 9.2), with the link `lead` pointing at the
   clone's skill: every step gives its expected result, or each miss is
   fixed and its step repeated.
8. **Landing** (section 11, step 4), the link back, 013's readme and
   log, 013-01's status line (choice 8): a new session lists the new
   description and `/lead` starts.
9. **The first real night**: Frans has the summary before 07:00, the
   audit shows no gap without a cause, and the check-in's cost is in
   013-04.


## 13. For Frans to decide

Each with the recommendation the plan assumes. Frans chose all ten as
recommended (2026-11-23).

1. **The class lists** of section 3. Class 3 is Frans's list; class 1 is
   his examples and this plan's additions (a new 028 entry, a fix of a
   test or harness, starting the three run scripts, the lead's own run
   data). Recommended: as written.
2. **A push to `main`**: class 1 at any hour, as today, after the gates
   and the privacy check; or commits wait unpushed for 07:00.
   Recommended: class 1, though a push cannot be taken back: the checks
   are the same at any hour.
3. **The class 2 time**: at least 30 minutes, an hour as a rule, met by
   the next check-in. Recommended: so. Over a weekend the defaults add
   up until Monday 07:00.
4. **A Fable agent**: class 2, or class 1 when the week is 15 points
   below the limit. Recommended: class 2.
5. **The limit at the week's reset**: back to 50 %, or the last number
   stays. Recommended: back to 50 %; a 95 % of a week's last day would
   otherwise govern the next week.
6. **The check-in**: every 30 minutes, or hourly. Recommended: 30
   minutes; hourly if an idle one costs over a tenth of a point.
7. **Agents at a time.** Recommended: four, two at `tight`.
8. **013-01**: marked done, as the record and the conductor's home, or
   kept open. Recommended: marked done.
9. **A dead session**: accepted, with `news.md` and `/lead` in the
   morning; or a test of automatic revival (013-02, section 11); or the
   lead in a terminal outside VS Code. Recommended: accepted, until it
   happens.
10. **During a timing run**: no agents, or agents that only read and
    write. Recommended: none.
