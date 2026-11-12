# 027-01. docs/ as of 2026-11-12, a snapshot

Created 2026-11-12 by Frans Lundberg. Status: done.

The documents that were `docs/` before the items existed and while they
grew: the current state of BergDB in words, as it was kept up to date
until 2026-11-12. Moved from `docs/` on 2026-11-12 (Frans, 14:27: "I
would like to remove everything from docs/ now. [...] We then have a
reference to them, we don't update them, but they are there for
reference, a snapshot in time."), not updated since: a snapshot for
reference. The maintained description of the algorithms is 027, which is
being written; until a section of it is, these files are the best
description of what they cover, as of this date.

The files keep their names; `git log --follow` gives their history. Only
their relative links were changed, so that they still resolve from here;
their text is as it was.

* [levels.md](levels.md). BergDB's features level by level (Level 0, the
  multiversion map in memory, to Level 4, eviction): what each level does,
  how the Java code does it, what checks it, its limits, and the evidence
  by item ID; failures (section 3), durability (8), replication (9), and
  the Pub API's objects and user indexes (11). Its history until
  2026-10-26 is 011-04.
* [sis-model.md](sis-model.md). Self-indexed streams, the abstract model
  that `lean/` formalizes and proves: the structure, the stream, the
  algorithm, startup, the theorems T1 and T2, the obligations of an
  implementation, and the physical layer with eviction and reclaim
  (section 15). `lean/`'s comments cite its sections.
* [sources/](sources/). Frans's documents of 2012 to 2016 that the model
  builds on: `startup.md` and `startup-1604.md` (2016), the paper draft
  `self-indexed_streams_v5_130704.pdf` (2013) and `2015-algos.pdf`.
* [docs-readme.md](docs-readme.md). `docs/readme.md` as it was: what each
  file was, and where the files of the 2026-10-26 cleanup (006-07) went.

Not here:

* `log.md`, the development log, stayed in `docs/` and is still written
  (Frans, 2026-11-12, 14:32: "Some type of log is good to have. Let's keep
  log.md for now.").
* `trace-format.md` is 027-02, kept current, since the exporter and the
  checkers implement it (see 027's readme).

Frans on the levels, 2026-11-12, 14:27: "the division of functionality
into "levels" was very useful to get the old code base stability. There
were bugs all over and it really helped. Now, I don't know how important
this division it." The level scripts (`java/stress/level1.sh` to
`level4.sh`) still follow the levels; whether 027 keeps them as its
structure is open (027, "Planned sections").
