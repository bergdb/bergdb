021-02. Fix: lean/README.md: a progress log, wide tables and a "Written by Claude" line
=======================================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-07 by Frans Lundberg.

What: `lean/README.md` (1,275 lines on `main` at 8682edd) breaks three of
AGENTS.md's rules, and `docs/sis-model.md` shares the third:

1. Its section Status (line 519 to the end, about 750 lines) is a dated
   progress log, from "2026-10-12. Milestone 1" on. AGENTS.md: "progress
   logs ... belong in an item, not in `java/`, `lean/` or `docs/`".
2. Its two tables in "What to read" (lines 203 and 223 on: File,
   Contents, sis-model.md; File, Contents) have 57 rows over 120
   characters, the longest 1,502 (`SIS/Basic.lean`'s row). AGENTS.md's
   table rules: data rows of at most 100 characters, 120 at most, else
   split the table or use a list.
3. Its line 4: "Started 2026-10-12. Written by Claude for Frans Lundberg."
   `docs/sis-model.md`'s line 4 says the same: "Draft 2, 2026-10-12.
   Written by Claude for Frans Lundberg."

Why: from agent d30's read-through of the documentation for release
2026.3 (006-13's progress, 12:44; 165bb9e), not fixed before the release:
006-13, section 5, "For Frans to decide (in the morning)", point 1.
Recommended there: after the release, and the "Written by Claude" lines
as 006-12's point 10, option (b), was done (Frans, 2026-11-06, 11:35:
the lines moved from the headers of 018-02, 018-04 and 018-07 to each
item's Log; 006-13, W1, point 10; 4b9f720).

Frans, 2026-11-07, 08:00: "For a., do as recommended."

Frans: none. The defaults (KISS, 010-P13), as point 10's (b): these two
files are not items, so each line goes to a log:

1. The dated log of Status moves, as it is, to a new subitem of
   011-docs-archive (as 006-07 moved the documents of `docs/` that no item
   owns there; a line in 011's Files and its Log). `lean/README.md`'s
   Status keeps the current state without dates (what is defined, proved
   and checked, and the open obligations) and cites the subitem by its ID.
   References to "lean/README.md, Status" in `docs/`, `lean/` and
   `java/` comments that mean an entry of the log are made to cite the
   subitem; old items are history and are left as they are.
2. The two tables become lists (one item per file, its contents, its
   sections of sis-model.md), or narrower tables with the long contents
   in a list below; no data row over 120 characters, most at 100 or less.
3. `lean/README.md`'s line goes into the moved log, as its first entry:
   "2026-10-12. Started. Written by Claude for Frans Lundberg. (Moved
   here from lean/README.md's header on <date>, at Frans's word,
   2026-11-07, 08:00: 006-13, section 5, morning list, point 1; as
   006-12, section 8, point 10, option (b).)" `docs/sis-model.md`'s line
   goes into `docs/log.md` (the development log, kept: docs/readme.md) as
   a dated entry of 2026-10-12 with the same note; the header keeps "Draft
   2, 2026-10-12." `docs/log.md`'s own "Written by Claude (Opus 5.5)
   agents ..." (2026-10-29, item 012) is already in a log and stays.

Done when: the three done; `lean/README.md` and `docs/sis-model.md` name
no AI in their text; no table row over 120 characters in
`lean/README.md`; every link and section reference that the move touches
works (grep for "Status" and the file's anchors). Text only, with no
`.lean` file changed, so no gate.

First step: read `lean/README.md`'s Status and decide where its current
state ends and its log begins; list the references to it (`grep -rn
'README.md' docs lean java/src java/stress`).


Log
---

2026-11-07. Registered by coord-1106 from 006-13's morning list, point 1,
at Frans's word (2026-11-07, 08:00).

2026-11-07. Taken by agent f13 of coord-1107 (006-14).

2026-11-07. Done by agent f13 of coord-1107, with the defaults:

1. `lean/README.md`'s Status (its 750 lines, a dated log from 2026-10-12
   to 2026-10-28) moved, as it was, to the new subitem 011-12
   (`items/011-docs-archive/12-lean-status-log.md`; its three kinds of
   links fixed for the new place; a line in 011's Files and its Log). The
   README's Status now holds the current state without dates: what is
   proved (Level 2, stages 1 to 3 of 001, the bounds, each with its
   theorems), what is checked by running, and the three open points of
   "Not done", taken from the log's last two paragraphs; it cites 011-12.
   References that meant the log: `docs/sis-model.md`'s review note of
   2026-10-13 and its section 13's "lean/README.md, the changes to the
   trusted part" now cite 011-12. No reference in `lean/`, `java/` or
   `docs/levels.md` meant the log (levels.md's cites the README's
   introduction, which stays). Old items are left as they are.
2. The two tables of "What to read" are lists, one item per file: the
   file, its sections of sis-model.md (or "not in sis-model.md" with the
   document that has it), then its contents, word for word; the four paths
   to items in them became IDs (005-62, 007-01, 007-08, 009-02).
   `lean/README.md` has no table now and no line over 100 characters but
   one of prose (108, in the introduction).
3. `lean/README.md`'s line 4 is the first entry of 011-12's log, with the
   note. `docs/sis-model.md`'s line 4 is now "Draft 2, 2026-10-12."; its
   "Written by Claude" went to `docs/log.md` as an entry of 2026-10-12, and
   section 15's first line, "Added 2026-10-18 by Claude (Opus 5.5, Claude
   Code)", the same way as an entry of 2026-10-18 (the "Done when" asks
   that sis-model.md name no AI). The README's "review-13-claude's
   `R4Bridge.lean`" (a file of the f1 repository) became "the
   `R4Bridge.lean` of F1-008-13's review".

Not changed: the README's introduction still tells its history in "Since
bergdb item ... (date)" paragraphs; not in this entry's scope. Text only,
no `.lean` file changed, so no gate.
