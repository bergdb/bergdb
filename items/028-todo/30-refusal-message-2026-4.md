028-30. Investigate: release 2026.4's refusal message names a release that cannot help
======================================================================================

Status: open. Kind: Investigate. Frans: none.
Created 2026-11-19 by Frans Lundberg.

What: Release 2026.4, refusing a database of a newer format, says to read it
with release 2026.5, which a user of 2026.4's database cannot do in the
way the message suggests (noted by the user apps' work, 028-23). 2026.4
is released, so its message cannot change; what can change is what the
release notes and the documentation tell a user who meets it.

Why: A refusal must tell the user what to do (the refusals' messages, 028-15
for 2026.6).

Frans: none.

Done when: The message's exact text and the case that shows it are written down;
the notes of the next release, or 2026.4's Known issues, say what a user
who meets it should do; no code change unless a current message has the
same fault.

First step: Find the message in release 2026.4's code (its tag) and the case in
which it appears.


Log
---

2026-11-19. Registered by coord-1118 from a report of the day's work.
