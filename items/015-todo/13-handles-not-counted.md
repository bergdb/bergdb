015-13. Fix: the resident bytes count no handle, where 009-02, 4.7 counts them
=================================================================================

Status: open. Kind: Fix (decided). Created 2026-11-03 by Frans Lundberg.

For Frans; a known issue of 2026.2 until decided. Found by review R1
(016-06/R1 (items/016-release-2026-2/06-reviews/R1.md)), R1-F2, with a probe.

What: 009-02, 4.7 counts a live handle with its table entry (79 bytes)
and 32 bytes for each pointer that holds a handle. The code counts
neither (`Residents.bytesOf`, `added`; `Cache3`). In R1's probe that is
34 to 49 percent of the counted bytes, so a database uses that much more
memory than its budget, more with small nodes and small budgets. Not in
2026.1 (no handles).

Options: A, count them as 4.7 says (R1-F2's fix: `bytesOf` adds 32 per
handle pointer, `added` and `released` 79 per live handle); B, record in
009-02, section 9 and docs/levels.md, section 7 that the budget covers the
objects and their values only.

Recommendation: A after the release, with the eviction numbers measured
again (more eviction at a given budget); for 2026.2, the known issue in
the notes with the probe's figures.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-03, 17:18. Frans: "This seems straigh-forward. If it really is
straight-forward and you have a proposal, fix it before the release." So
option A, R1-F2's proposal, before the release, by agent K after 015-15.
