015-18. Implement: run night.sh large on the release, after 2026.2
==================================================================

Status: open. Kind: Implement. Created 2026-11-03 by Frans Lundberg.

What: `java/night.sh large` (the night run with the large conformance
set, about 6 hours) did not fit before release 2026.2's commit (016-08,
section 6). Frans, 2026-11-03, 17:18: "It can be run later. Let's just
ensure we remember to."

Done when: `night.sh large` has run on the release's commit (the tag
`release-2026.2`, or commit A) and printed its pass line, and the result is
in 016-08's results and in 2026.2's post-release notes if it finds a
fault.

First step: start it by hand on a quiet F53 after the release (016-08,
section 6, the commands), not overlapping another `night.sh`.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).
