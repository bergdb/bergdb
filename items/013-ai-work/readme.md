013-ai-work
===========

Created 2026-10-28 by Frans Lundberg. Status: open.

How AI agents work on BergDB: ways of working that have been tried and
worked, written so that Frans, Claude and other AI agents can follow them.
Each subitem describes one way of working; the work itself stays in its
own items.


Files
=====

* [01-night.md](01-night.md). 013-01, the unattended night: an AI session
  works from about noon to 07:00 the next morning without Frans. The roles,
  the plan, the ground rules, the day's development with subagents, how
  the work survives a usage limit, the quiet block of timed runs at night,
  the morning's write-up, and the lessons of the first night (006-09).
  [01-night/](01-night/) has the conductor script and an example of its
  steps file.
* [02-coordinator.md](02-coordinator.md). 013-02, the daily coordinator,
  superseded by 013-04 from 2026-11-23 and kept as the record:
  one session a day that Frans talks to and that runs the work through
  subagents, in three modes (attended, unattended, closing); a new one
  each morning; the shared things it owns; its state; how it resumes after
  a usage limit, a network outage or a dead session; effort and usage.
  [02-coordinator/skill/](02-coordinator/skill/) is the Claude Code
  skill `coordinator`, with the state file's template, the watchdog and
  the usage reader, linked from `~/.claude/skills/coordinator`.
* [03-model-comparison.md](03-model-comparison.md). 013-03, a dated
  Artificial Analysis comparison of GPT-6.1 Sol, GPT-6 Astra, Claude Opus,
  Sonnet and Haiku 5.5: intelligence, estimated task time, time to first
  token, time for a 500-token answer and API-equivalent cost per task;
  the model choices made from it.
* [04-lead.md](04-lead.md). 013-04, the lead: the daily session Frans
  works with, 013-02's coordinator under a new name. [04-lead/skill/](04-lead/skill/)
  is the Claude Code skill `lead`, a copy of 013-02's skill with the names
  changed, linked from `~/.claude/skills/lead`; [04-lead/plan.md](04-lead/plan.md)
  is the plan for its cleanup.


Log
===

2026-10-28. Created the item, at Frans's request ("Create a new item
called 013-ai-work. Create a subitem 01-night. In 013-01 describe the
unattended nightly work."), with 013-01, by Claude (Opus 5.5, Claude
Code), from 006-09.

2026-10-28. 013-02, the daily coordinator, at Frans's request ("Add this
plan to a new 013-02 item. Describe it there. Also implement the
Claude-specific stuff that is needed for the coordinator skill."), by
Claude (Opus 5.5, Claude Code), from a conversation with Frans the same
morning. The skill is installed by a link in `~/.claude/skills/`; a new
session found it. The watchdog was tested with a stand-in for
`tools/news.sh`: a live and a dead process, an old heartbeat, a stop by
`kill`. The skill itself has not run yet.

2026-10-28. `usage.sh`, at Frans's request ("The 5-hour usage limit: the
coordinator can't see how much usage is left. Solve this somehow."): it
reads the plan's usage through Claude Code's `/usage`, run headless, with
no model call, and gives a level for pacing (013-02, section 9). Tested
online, and with no binary. Plenty changed the same day, at Frans's
request, to the week at most 15 points ahead of its time (was 10).

2026-10-28. The coordinator's effort follows its mode, at Frans's
request: xhigh attended, max unattended (013-02, section 9). Frans
switches it with `/effort`: a scheduled `/effort xhigh` reached the
model as plain text, so the coordinator cannot switch by itself.

2026-10-30. 013-03, the model comparison, at Frans's request, by Codex:
the chat's table extended with both response timings and the Sonnet and
Haiku configurations discussed, refreshed from AA Intelligence Index
v5.0, with dated sources and the distinction between API-equivalent cost
and subscription usage.

2026-11-03. Effort xhigh for everything, the coordinator in every mode
and every subagent, at Frans's request ("Effort level should be xhigh by
default for everything unless explicitely told by Frans to use something
else. If usage is tight or limit, use effort level High. Do not use
Medium."): high when usage is tight or limit, another level only at
Frans's word, never medium (013-02, section 9; the skill; 013-01,
section 4). This replaces max unattended and max for hard problems.

2026-11-07. Subagents at high by default, at Frans's request (07:51:
"Let's change it (if needed) so it starts subagents with effort level
High as default. Unless I say otherwise, of course. That is the default,
but the coordinator is allowed to use XHigh for subagents with hard tasks
such as finding Lean proofs or coding for correct concurrency."): xhigh
for such a task at the coordinator's judgment, when usage is plenty or
normal; the coordinator itself stays at xhigh, all at high when usage is
tight or limit (013-02, section 9; the skill; 013-01, section 4). This
replaces xhigh for every subagent.

2026-11-17. 013-03 rewritten for the public repository (029): the
comparison kept (the table, the figures, the method), the personal and
business details removed; the earlier versions are not published.

2026-11-23. 013-04, the lead, by Claude (Opus 5.5, Claude Code). Frans
renamed the coordinator to the lead and started it as subitem 013-04, with
the skill `lead`, a copy of 013-02's skill with the names changed; at its
start it also finds a coordinator that is not closed. 013-02 is done and
kept as the record of the coordinator (2026-10-28 to 2026-11-22), not
updated; it still explains the mechanism until 013-04 is rewritten.

2026-11-23. 013-04's plan for the cleanup of the skill,
[04-lead/plan.md](04-lead/plan.md), by Claude (Fable 5.2, Claude Code):
no attended and unattended modes; decisions in three classes (the lead
decides; it goes ahead by default at a stated time; it waits for Frans);
07:00 on weekdays as the fixed point to consolidate; no phone
notifications (Frans, 2026-11-23). Frans chose the plan's ten
recommendations the same day. AGENTS.md and the headers of `night.sh` and
`week.sh` name the lead (013-04); the link `~/.claude/skills/coordinator`
is removed.
