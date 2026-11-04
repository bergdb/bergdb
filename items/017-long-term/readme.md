017-long-term
=============

Created 2026-11-04 by Frans Lundberg. Status: open.

The long-term topics of BergDB: open-ended questions, directions and
possible work that need Frans's thinking as input, have no fixed "Done
when", and may never be done, such as publishing BergDB or block storage.
Notes about them are kept here, one subitem per topic. The todo lists
(015) hold bounded work that an AI agent can do together with Frans now;
this item holds the rest.


Rules
=====

* A topic is a subitem: what it is about, why it matters, what is known,
  the open questions, and Frans's notes.
* A topic's state is one of: open (notes only), parked, promoted (to an
  item of its own when it grows into real work with subitems, linked from
  here), or dropped (with the reason). Its own `Status:` line says which.
* An AI agent does not take up a topic on its own. A topic is taken up one
  at a time with Frans; a bounded piece of it can become an entry of a todo
  list.
* An entry of 005 or 015 that turns out to be long-term is moved here by
  Frans, one at a time: its contents become a new subitem here, its row
  moves to its list's Closed table (status moved), and its file stays as a
  short note with a link, so links to it keep working.


Files
=====

* 017-01. Not in the public repository.
* [017-02](02-publication/readme.md). The literature and the options for
  a publication: self-indexed streams, BergDB as a whole, the
  verification, and the code-only transactions. Moved from 005-06 on
  2026-11-04. Open; explored now, Frans decides later.
* [017-03](03-replication/readme.md). Replication: ways to implement it.
  The design that BergDB had until 2026-11-04, when it was removed (005-11,
  Frans: "A with C2 now"), Frans's question on durability and waiting for
  replication, and the options for a future design. Open; notes only.
* [017-04](04-cost-bounds/readme.md). Cost bounds beyond startup: the
  problem statement's Q1 the lookup bound, Q2 long keys, Q3 the cost
  model, Q5 the write overhead and Q8 the space bound with reclaim, with
  the measurements for Q5 and Q8. Moved from 005-54 on 2026-11-04. Open;
  notes only.


Log
===

2026-11-04. Created the item, at Frans's request, for the long-term
topics that are not ordinary todos.

2026-11-04. 017-01, what to do with BergDB, moved from 005-05 by
Frans, who asked for the options to be prepared now and will decide
later.

2026-11-04. 017-02, the literature and the options for a publication,
moved from 005-06 by Frans, who asked for an exploration now: a paper on
self-indexed streams, the other options, and whether the code-only
approach to transactions (STM and historic queries) is novel.

2026-11-04. 017-03, replication, created when 005-11 was decided ("A with
C2 now") and replication was removed from BergDB: the removed design in
full, Frans's question, and the options for a future design.

2026-11-04. 017-04, cost bounds beyond startup, moved from 005-54 by
Frans: not to item 007, which is concrete work with a plan (T3 proved, T4
a bound on D for startup) that five general theory questions would keep
open with no end in sight; and not closed, as Q1 points at real behaviour
(a tree split but never merged keeps its largest size after mass deletes)
and Q5 and Q8 have measurements that could become the accepted answer. A
question that becomes a real theorem goes to 007 then.
