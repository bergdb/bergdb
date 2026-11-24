# 006-34 Day work, 24 November 2026

Created 2026-11-24 by Frans Lundberg. Status: open. The plan for the
lead's day of 2026-11-24 (lead-1124), a Tuesday, and its night to
Wednesday 07:00: the progress and the outcome. The way of working is
013-04's (the lead), on its new skill since 07:45 (`77d7ec1d`).


## 1. The request

* The release 2026.6: 026-27, steps 12 to 16, with Frans.
* After the release: 026 closed, its subitems' statuses set; the points
  of 006-33, section 5, that wait for Frans.


## 2. Decisions

Frans, 2026-11-24:

* 013-04's new skill lands without a separate review and is tested in
  use from lead-1124 on (006-33, point 5).
* README.md for after the release: the values a key holds, the
  deterministic stream, "Try it" before "Status", the core algorithms
  proved as the list's last point; the release notes name the platforms
  tested, 2026.6 not on Windows.
* The release: A into `main`, commit B, the tag `release-2026.6` on A,
  the GitHub release (026-27, steps 12 to 15).
* bergdb.org for 2026.6, with wider lines, coloured Java examples and
  links in the text's colour.
* 026 done; its subitems' statuses set by an agent on Opus, xhigh.
* 006-33, points 2 to 4, as recommended there: F4 and F7 accepted for
  2026.6; the three 028 entries of 030-39 registered. Point 4 otherwise:
  028-07's date race is RB-004, S4; every fault that can be considered a
  bug is registered, also one possible in theory only. Point 6: SUMMARY
  DUE kept as it is.
* Bugs: every fault that can be considered a bug is registered in 033,
  also one possible in theory only; no release is made with a known bug,
  and fixing bugs is always priority 1 (an exception is Frans's,
  recorded); each release's notes list the bugs known in it, later
  ones in an "After the release" section; README.md and bergdb.org list
  none.
* Releases in general: item 034, the process, a checklist and the
  scripts in one place.
* RB-005: option A (028-50). 028-47: no change; F1 and F3 registered.
* No theme or scope for 2026.7 now: they settle as the work does.
* The lead stays interactive: long work, landing included, goes to
  agents.


## 3. Progress

* 07:45 013-04's new skill landed (`77d7ec1d`); lead-1124 moved to it.
* 09:32 026-27 step 12: A merged into `main` (`f281431a`), pushed.
* 09:38 Step 13: commit B `024ccd31`, BEFORE COMMIT OK, pushed.
* 09:45 Step 14: the tag `release-2026.6` on A, pushed (Frans's word).
* 09:47 Step 15: the GitHub release; the files downloaded and checked
  against SHA256SUMS; the tag's archive builds.
* 09:51 bergdb.org for 2026.6 (an agent, Opus high), pushed; 10:38 and
  10:55 its look changed (Frans).
* 11:05 Two agents, Opus xhigh: 026's subitems and 026 done (step 16);
  the three 028 entries of 030-39.
* 11:12 028-44 to 028-46 landed (`3bcec8f5`); 026 done, its subitems'
  statuses set (`e78d82f7`); 026-03 and 026-04 carried to 031.
* RB-004 registered in 033; README.md: 2026.6 fixes RB-001 to RB-004.
* 11:20 After 026 (Frans): RB-004 in 2026.6's notes and on the GitHub
  release; 026-14 to 031; the versioning rule and the corpus to 032;
  028-47 registered (`e1f42edb`).
* 11:25 Open 028 entries (Frans: the lead works on them): four agents,
  each in a clone: 028-44 (Opus xhigh), 028-45, 028-46 and 028-01 (Opus
  high); the lead lands them after their gates and the combined gate.
* 12:26 Frans chose 028-45's option A (RB-005's fix): 028-50 registered,
  an agent in a clone.
* 12:30 Frans: 028-47 no change; F1 and F3 registered as 028-51 and 028-52.


* 12:20 to 13:37: 028-44 and the 028-47 study, 028-52, 028-50 (RB-005
  fixed on `main`), the "After the release" sections, 034, and 028-51
  (RB-006, S4, `maintain()`'s stall, found and fixed on `main`) landed;
  033 up to date with counts for 2026.6; 028-53 registered and taken.

* 14:09 028-53 investigated: the idle rewriting under `maintain()` a
  cost, not a released bug; RB-007, S4, found (writes made while an
  iteration waits for its cut are kept for good); 028-53 waits for
  Frans's choice (`215dde0b`). 14:24 028-49 landed: `body.sh` in 034's
  scripts (`72326123`).
* 14:48 to 17:50 `night.sh` on `72326123`: NIGHT OK (183 minutes).
* 16:45 by default, 17:13 confirmed by Frans: option A of 028-53
  designed, with a prototype on a branch; nothing of it lands without
  Frans (`70807233`). 17:28 Frans: the choice waits for the morning.
* 18:18 to 21:00 028-19 (Frans's decision of 2026-11-19): reclaim's pace
  with PE explained, PE's short path faster with the trees unchanged
  (`4ac71aee`). 21:18 to 00:19 `night.sh` on `4ac71aee`: NIGHT OK (181
  minutes).

## 4. Outcome

Written 2026-11-25, 00:50.

**Done.** Release 2026.6 is made (026-27, steps 12 to 16): the tag
`release-2026.6` on A `bbcd802f`, commit B `024ccd31`, the GitHub
release with the jar, the Javadoc zip and SHA256SUMS; bergdb.org and
README.md for 2026.6; 026, 024 and 030-38 done. A review of the release
(20 findings, none severe) is fixed and published. Item 034 holds the
release process, its checklist and its scripts. 013-04's new skill runs
the lead since 07:45. Landed and gated: 028-01 and 028-48 (the conflict
check), 028-44 (shape faults fail a contract trace), 028-45 and 028-50
(RB-005 found and fixed on `main`), 028-46 (joins above the proved
heights tested at node sizes 30 and 62), 028-47 (studied; no change),
028-49 (the release body), 028-51 (RB-006 found and fixed on `main`),
028-52 (a gate fixed) and 028-19 (reclaim's pace explained, PE faster).
Released bugs registered: RB-004 to RB-007 (033), each named in the
notes of the releases that have it. `night.sh` passed twice, the last on
`4ac71aee`, all of the day's code.

**By default.** 16:45: 028-53's option A designed, not landed (Frans
agreed at 17:13).

**Waiting for Frans.** 028-53 / RB-007 (S4, open in 2026.5, 2026.6 and
`main`): the simplest A (a mark of the application's last write in the
table's last row; about 80 lines; the stream's bytes change), A with K,
B (one line; quiet databases with live values rewrite them under
`maintain()`), or C. Recommended: the simplest A. Under 034-01 a release
waits for RB-007's fix or Frans's exception.

**Proposed next.** RB-007's fix as Frans chooses, first (bugs are
priority 1); then what 2026.7's work brings, with no theme set yet
(031).

