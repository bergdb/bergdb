034-releases
============

Created 2026-11-24 by Frans Lundberg. Status: open.

How BergDB's releases are made, for every release: one maintained
process, so that every release is made the same way and nothing is
forgotten (Frans, 2026-11-24). A release item, from 031 (2026.7) on,
holds its plan, scope and decisions, not the process: it points here
for how the release is made, and says only where it departs from it. A
change of the process is made here, dated, and holds from the next
release on.


Files
=====

* 01-process.md. 034-01, the release process, maintained: the rules
  (among them no release with a known bug, Frans, 2026-11-24), who does
  what, the planning, the steps 1 to 13 from the release plan to after
  the release, the section "After the release" of the notes, and the
  scripts with their smoke test.
* 02-checklist.md. 034-02, the checklist, maintained: everything to
  check or update at and after a release, one line each with how it is
  checked, by a script's line or by hand; the lines missing in 2026.6
  are marked, the reason for the list.
* scripts/. The release scripts: `set-buildinfo.sh`, `to-main.sh`,
  `release.sh` and those it calls (`build-a.sh`, `finish.sh`,
  `notes.sh`, `stage-b.sh`, `commit-b.sh`). Moved from 026-27's
  directory on 2026-11-24 and made release-independent (034-01, section
  6).


Log
===

2026-11-24. Created the item (Frans, 13:05): one standing item for
releases. 034-01 and 034-02 written from 026's "How the release is
made", 026-27, 024-38, 033's rules, AGENTS.md's release runs and 028-49;
the rule of no release with a known bug added (Frans, 13:12). The
release scripts moved here from 026-27's directory (git mv) and made
release-independent: the release from A's `BuildInfo`, the work
directory from the date, the release item found in `items/`; smoke-tested
on scratch repositories (034-01, section 6). 028-49, the GitHub
release's body with absolute links, is to be made in these scripts.
