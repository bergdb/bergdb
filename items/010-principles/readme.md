010-principles
==============

Created 2026-10-26 by Frans Lundberg. Status: open.

BergDB's design principles, in Frans's words: what BergDB promises about
its behaviour, beyond the results of its operations. The principles guide
the design and the decisions of other items; this item records them, where
BergDB stands against them today, and the open questions.


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
  and where BergDB deviates from it today.
* [02-principles-2012.md](02-principles-2012.md). 010-02, the principles
  Frans wrote down from 2008 to 2017 (notes, logs, code, the old website),
  quoted with their sources: how they support, refine or contradict P1 to
  P4, the reasons behind P3, the other principles, and candidates for 01.
* [03-startup-distance-on-the-fly.md](03-startup-distance-on-the-fly.md).
  010-03, moved to [005-53](../005-todo/53-startup-distance-on-the-fly.md):
  a link in its place.


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
