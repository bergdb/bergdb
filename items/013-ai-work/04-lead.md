# 013-04 The lead

Created 2026-11-23 by Claude (Opus 5.5, Claude Code), at Frans's request.
Status: open.

The *lead* is the daily AI session Frans works with: he talks to it, and it
runs most of the work through subagents. It is the coordinator of 013-02
under a new name (Frans, 2026-11-23), and the lead session of 013-01 is the
same role.

The lead started as a copy of 013-02's skill with the names changed: the
skill `lead`, the session `lead-MMDD`, the state in
`/Users/f/fl/bench/lead/`. One step differs: at the start, the lead looks
for the previous session in both `/Users/f/fl/bench/lead/` and
`/Users/f/fl/bench/coord/`, so that the first lead can close the last
coordinator. A cleanup of the skill is planned in
[04-lead/plan.md](04-lead/plan.md). Until this subitem is rewritten, 013-02
explains the mechanism: the modes, the roles, the shared things, the state,
the check-ins, the watchdog, effort and usage.

## Files

* [04-lead/skill/](04-lead/skill/), the Claude Code skill `lead`:
  * [SKILL.md](04-lead/skill/SKILL.md), the procedures: start, attended,
    unattended, closing, check-in, resume;
  * [state-template.md](04-lead/skill/state-template.md), the template of
    the state file;
  * [usage.sh](04-lead/skill/usage.sh), the usage reader;
  * [watchdog.sh](04-lead/skill/watchdog.sh), the watchdog.
* [04-lead/plan.md](04-lead/plan.md), the plan for the cleanup of the skill.

Installed by a link:

    ln -s /Users/f/fl/repos/bergdb/items/013-ai-work/04-lead/skill ~/.claude/skills/lead
