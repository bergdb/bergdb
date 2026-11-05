017-long-term
=============

Created 2026-11-04 by Frans Lundberg. Status: open.

The long-term topics of BergDB: open-ended questions, directions and
possible work that need Frans's thinking as input, have no fixed "Done
when", and may never be done, such as publishing BergDB or block storage.
Notes about them are kept here, one subitem per topic. The todo lists
(015, and 019 since 2026-11-05) hold bounded work that an AI agent can do
together with Frans now; this item holds the rest.


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
* A small idea to consider, too small for a topic of its own, is a
  section of 017-07, "To consider" (Frans, 2026-11-05).
* An entry of 005, 015 or 019 that turns out to be long-term is moved
  here by Frans, one at a time: its contents become a new subitem here,
  its row moves to its list's Closed table (status moved), and its file
  stays as a short note with a link, so links to it keep working.


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
* [017-05](05-block-storage/readme.md). Block storage: the stream on a
  raw block device without a file system, as a ring of a fixed size whose
  front is given up when the room is needed (retention by space); in Java,
  and in a C or C++ clone on a Linux device. Moved from 005-60 on
  2026-11-04. Open; notes only.
* [017-06](06-overload/readme.md). Overload, backpressure and admission
  control: whether BergDB needs database-wide admission control and
  backpressure for CPU, reads and memory under overload, which controls
  belong in BergDB and which in the application, and the behaviour at and
  above capacity and after it. Split from 005-81 on 2026-11-04. And the
  transaction retries ([retries.md](06-overload/retries.md)), moved from
  015-88 on 2026-11-05, with Frans's question whether `rw()` should ever
  give up under overload. Open; notes only.
* [017-07](07-to-consider/readme.md). To consider: small ideas that
  Frans may take up some day, one section each; first, a get that always
  copies a `byte[]` value (from 019-03); second, startupDistance in the
  meta block rather than in an internal KV (from 015-87's F1); third,
  refusing a value transformation's result above the value limit (from
  015-51). Open; a collection.


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

2026-11-04. 017-05, block storage, moved from 005-60 by Frans, in his
words: "This is a big thing, long term, open-ended. Not a todo for 005."

2026-11-04. 017-06, overload, backpressure and admission control, split
from 005-81 by Frans (19:11): "005-81, I like your idea to split this. So,
split it." The retry fix stays in 005-81, narrowed to bounded work; the
broad, open-ended question of admission control and backpressure under
overload is this topic.

2026-11-05. 017-07, "To consider", created at Frans's request (12:16)
for small ideas that are not todos for the next release; its first
section is 019-03, a get that always copies a `byte[]` value, moved from
019.

2026-11-05. The transaction retries moved to 017-06 from 015-88 (005-81
until that morning) by Frans (14:12), as 06-overload/retries.md, with his
question whether `rw()` should ever give up under overload; 015-88 keeps
only the cap of the retry sleep at 640 ms for release 2026.3 and stays
open until it lands.

2026-11-05. 017-07, section 3, refusing a value transformation's result
above the value limit, added at Frans's request (21:03) when he decided
015-51: such a result is the caller's fault and fails the database.
