010-principles
==============

Created 2026-10-26 by Frans Lundberg. Status: open.

BergDB's design principles, in Frans's words: what BergDB promises about
its behaviour, beyond the results of its operations. The principles guide
the design and the decisions of other items; this item records them, how
they are applied in BergDB's development, and the open questions. Mostly
they are followed; a few simple principles will always need exceptions,
and each exception is justified.


Principles
==========

In brief; [01-principles.md](01-principles.md) has each in full, with its
sources and how it is applied: where it is followed, and the exceptions
and why they are made.

* **P1**. *No stop-the-world*. No get or commit waits long because BergDB does
  work for the whole database at once, readers included; the target is a
  worst case of about 20 ms.
* **P2**. *A deterministic stream*. The stream's bytes depend only on the
  transactions, their contents and their order.
* **P3**. *Calm when not used*. BergDB uses CPU, I/O and wake-ups only for work
  that the application's calls start.
* **P4**. *Maintenance proportional to the user's work*. The maintenance a call
  carries is bounded by, and in proportion to, the work of the call.
* **P5**. *Bounded startup*. Startup time does not grow with the size of the
  database or how long it has run.
* **P6**. *No interruption for changes*. Indexes, replicas and settings change
  while the database runs; a large change goes in steps.
* **P7**. *A failed database stops*. After an I/O error, corrupt data or a bug,
  every call throws until the application restarts the database.
* **P8**. *Determinism beyond the stream*. Where possible, memory, eviction and
  work are the same in each run of the same calls, independent of the JVM
  and timing.
* **P9**. *No global state*. Several databases run in one JVM without affecting
  each other.
* **P10**. *No administration, few settings*. The defaults work; no tuning is
  needed for good performance.
* **P11**. *Simple before optimal*. Simple, correct code comes before the last
  bit of speed.
* **P12**. *A small Core Layer*. All data passes through four methods (`getOne`,
  `getMany`, `getTrans`, `execute`); what can be built on top is built on
  top.
* **P13**. *KISS*. Keep it simple: the design, the API and its error model,
  the code, the tests and the tools. Also with AI, which can sustain more
  complexity.


Names
=====

* A principle is named P1, P2 and so on, all in one file,
  [01-principles.md](01-principles.md). In this item, `P1` is enough.
  Elsewhere, write `010-P1`: a bare `P4` means other things in other items
  (009's "P4's soak", 005-11's findings), and `010-01` is the subitem, the
  file.
* A principle's number is stable. Never reuse a number and do not fill
  gaps; a dropped principle keeps its number, so that references from
  other items stay right.


Files
=====

* [01-principles.md](01-principles.md). 010-01, the principles P1 to P12:
  no stop-the-world (for readers too), a deterministic stream, calm when
  not used, maintenance proportional to the user's work, bounded startup,
  no interruption for changes, a failed database stops, determinism beyond
  the stream, no global state, no administration, simple before optimal,
  and a small Core Layer. For each, what it means, where it comes from,
  and how it is applied, with its exceptions.
* [02-principles-2012.md](02-principles-2012.md). 010-02, the principles
  Frans wrote down from 2008 to 2017 (notes, logs, code, the old website),
  quoted with their sources: how they support, refine or contradict P1 to
  P4, the reasons behind P3, the other principles, and candidates for 01.
* 010-03 was removed on 2026-10-27; its contents are in
  [005-53](../005-todo/53-startup-distance-on-the-fly.md). The number is not
  reused.


Log
===

2026-10-26. Created the item, at Frans's request ("Create a new bergdb item
010 for principles."), with 010-01 and the four principles he gave.

2026-10-26. Added 010-02, the principles of the 2012 era in the old
sources, at Frans's request ("Start a new agent in the background that
searches pre-2026 bergdb, this repo and F1-007 if needed, for principles
from the 2012 era."). All four of 01 are there, from 2009 to 2015; eight
candidates for 01 at its end.

2026-10-26. Frans's decisions on 010-02's candidates, written into 01:
1 became P5 (bounded startup, without the one second), 2 was merged into
P1 (no stop-the-world for readers; short waits for a lock are fine), 3
became P6, 4 became P7 (a failed database stops; deterministic transactions
went into P2), 5 became P8, 6 became P9, 7 became P10, and 8 became P11,
named "Simple before optimal". Also his rule for all of them: a principle
may be broken if we must, and each deviation is documented in 01.

2026-10-26. Added 010-03, the startup distance on the fly, by a subagent
(Claude, Opus 5.5) at Frans's request ("On-the-fly changes to startup
distance used to be supported in the 2012 era. Have a look at this with a
subagent so it does not block our discussion."). It came in 2013-04, in the
core and through JMX, never in the Pub API. Also 005-52 registered, from
P6: the cache size changed while the database runs.

2026-10-26. 010-03 moved to a new entry, 005-53, to be investigated
properly, at Frans's request ("Move 03 contents from 010 principles to a
new item in 005. This should be investigated properly. In a separate work
item."). Its contents are 005-53's `history.md`; 03 keeps its number, as a
link.

2026-10-26. Added P12, a small Core Layer, at Frans's request ("Add P12 as
proposed."): the Core Data API (`getOne`, `getMany`, `getTrans`,
`execute`) within the larger Core API, kept small; the Core Layer does not
depend on the layers above. From the Db Javadoc of 2013, which Frans
updated the same day.

2026-10-26. P12's "Where BergDB stands" after 006-08, by Claude (Opus
5.5, Claude Code): the Core Layer builds alone and follows its
`package.html` lists, as `FileStreamPowerLossTester` moved from `stream`
to `core`; `dag`'s and `stream`'s lists fixed.

2026-10-27. Removed 010-03, the link to 005-53, and added the list of the
principles in brief to this readme, at Frans's request ("Remove the 03
document. Create a list with a brief summary of each principle directly in
the readme.md.").

2026-10-27. "Where BergDB deviates" rephrased as how the principles are
applied, at Frans's request ("It is more like how these principles are
applied to the development. Mostly they are followed and some excepts are
justified. That is the thing with principles. They should guide, but a few
simple principles will always need exceptions."). Also in 01's
introduction.

2026-10-30. P2's RW lifecycle clarified by Frans (005-70): reads and commit
belong to the same running database instance; after close/open, reread and
recompute. Reads should normally be within about one second of the current
time, as guidance, not a timeout. Lean's T2 compares a fixed transaction
sequence; pending read sets and STM admission are outside its scope.
