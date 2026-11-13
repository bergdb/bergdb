028-11. Fix: texts that disagree with the code, found by 027-11
================================================================

Status: done. Kind: Fix. Frans: P5 only.
Created 2026-11-13 by Frans Lundberg.

What: five texts that the review of 027-11 (Startup) found to disagree
with the code at 7e190010; the code is right in each (027-11, section 9,
"Found while writing"):

* 027-03, lines 415, 1116 and 1234: the creation as 264 bytes; it is 272
  (`Db.CREATION_LENGTH`, since 024-25).
* `java/stress/level1.sh`, lines 2 to 3 and 29 to 30: "startup always
  replays the whole stream"; since 005-49 the startup pos moves also
  below sd (027-11, section 1.11).
* 019-45, line 56: "the maps are garbage when the start returns"; Rule
  R's copy of newById stays (027-11, section 2). An item is history: a
  dated note, not an edit.
* `NodeCollection.java`, line 784, `linkToCanonical`'s Javadoc names
  only an `AssertionError` with 'check'; it also throws a
  `StreamFormatException` (027-11's comments list, item 10).
* 010-01, `01-principles.md`, line 357, P5's "Where BergDB stands": T3
  "not yet" for BergDB's own take; `T3_take` proves it since 007-08.

Why: 027 with Lean is the authority for the exact rule; texts that
disagree mislead the next reader (Frans, 2026-11-13, 11:09 and 13:01).

Frans: the P5 line only. Principles are edited only when Frans says so
(010-01); the entry proposes the sentence and Frans decides. The rest:
none.

Done when: the four texts say what the code does (027-03 corrected,
`level1.sh`'s header corrected, a dated note in 019-45, the Javadoc
fixed), `java/before-commit.sh` prints `BEFORE COMMIT OK` for the Java
comment, and P5's sentence is proposed to Frans in this entry.

First step: read each line on main.


Result
------

The four texts, each read on main at 55884666 and corrected:

* 027-03: the incomplete creation "at most 272 bytes" (264 until
  024-25); the creation's "264 bytes at format 5; 272 since 024-25" in
  012-02's section 8.2; `Db.CREATION_LENGTH` (272). The "creation's 264
  bytes" of C's vectors at format 5 a few lines on is right and stays.
* `java/stress/level1.sh`'s header: restart "by replaying nearly the whole
  stream (bergdb 027-11, section 1.11)"; step 4 "restarts by replay"; and
  why: since 005-49 the take writes a share of the dirty index nodes also
  while the startup section is shorter than the setting, so the startup
  pos moves now and then.
* 019-45: a dated note after the paragraph of the class histograms, and a
  Log line: Rule R's copy of newById stays for the process's life; the
  records, posMap and posToId are garbage. The text itself is unchanged.
* `NodeCollection.linkToCanonical`'s Javadoc: with 'check', a damaged
  prevPos throws a `StreamFormatException` (`checkLinkById`), and with or
  without it a pointer that names a node of another type does
  (`checkPointeeType`); an `@throws StreamFormatException` says both.

**For Frans: P5's sentence** (010-01, `01-principles.md`, P5's "Where
BergDB stands", the point on the take). Now:

> Proved in Lean for a policy that keeps up (T3), not yet for BergDB's
> own take: 007-03, step 4; [docs/levels.md](../../docs/levels.md),
> section 5, says so.

Proposed (it also mends the link, as `docs/levels.md` is 027-01's
`levels.md` since 2026-11-12):

> Proved in Lean for a policy that keeps up (T3), and for BergDB's own
> take since 2026-10-28 (`T3_take`, also with restarts; 007-08, 007-03's
> step 4): with a constant setting the section stays below 2 × sd; after
> a decrease it never grows, and it shrinks with every commit until it is
> below twice the new setting (`T3_take_decrease`).

Not applied: principles are edited only when Frans says so (010-01).

Log
---

2026-11-13. Registered by coord-1113, from 027-11's review.

2026-11-13. Done by an agent of coord-1113 (startbugs, branch
028-startbugs): 027-03, `level1.sh`'s header, a dated note in 019-45 and
`linkToCanonical`'s Javadoc corrected; P5's sentence proposed above, for
Frans; `java/before-commit.sh` printed `BEFORE COMMIT OK`.
