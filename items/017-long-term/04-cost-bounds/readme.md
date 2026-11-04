017-04. Cost bounds beyond startup
==================================

Status: open (notes only). Created 2026-10-26 as 005-54; moved here by
Frans on 2026-11-04, as a long-term topic. The questions, "Done when" and
"First step" below are 005-54's as they were when it moved.

What this topic holds: the bounds on BergDB's costs, other than startup's,
that the problem statement of 2026-10-12,
[011-01](../../011-docs-archive/01-problem.md), "Open questions", left
open: Q1 the lookup bound, Q2 long keys, Q3 the cost model, Q5 the write
overhead and Q8 the space bound with reclaim. They were carried forward as
005-54 when the problem statement left `docs/` (006-07, as Frans approved:
"Everything as recommended"). Of its other open questions, Q4 is item
007's, Q10 and Q11 are answered by item 001, and Q12 is 005-06's (now
017-02). These five have no other home.


Why it matters
--------------

A bound is what BergDB can promise its users about a cost, whatever the
size and the age of the database. Startup has one: T3 is proved in item
007, and T4, a bound on D, is planned there. The other costs are measured,
not derived: docs/levels.md, section 6, says that the bound on the stream
(R5, Q8) is measured, not derived, and cites 005-54 (now this topic).

Q1 is not only theory. Nodes are split but never merged, so a tree that
has grown large keeps its largest size after mass deletes, with nodes that
hold no live keys; a lookup's depth follows that largest size, not the
live keys, and the stream keeps the deleted keys (011-01, Q7).


What is known
-------------

* Startup: T3 proved and T4 planned, in item 007. 007-03, "After the
  plan", lists Q1, Q3 and Q5 with T4, as 005-54 named 007 their natural
  home.
* Q5 and Q8 have measurements, given with the questions below; either
  could become the accepted answer, if Frans accepts it.
* Q1: the multiversion B-tree merges underfull nodes and gets
  O(log_B n_t); BergDB does not merge.


Questions
---------

1. Q1, the lookup bound. What is n in O(log n)? Nodes are split but never
   merged, so the tree keeps the size it once had, and nodes with no live
   keys stay in it. Decide which bound BergDB promises; the multiversion
   B-tree merges underfull nodes and gets O(log_B n_t).
2. Q2, long keys. Each 7-byte key segment has its own tree; state the bound
   with the key length as a parameter.
3. Q3, the cost model. Define the cost of a lookup (node accesses, cache
   misses, stream reads) and the model behind "cache-aware".
4. Q5, write overhead. Derive it as a function of D, n, B and the update
   pattern. Measured since 2026-10-12: with uniform random updates, 6 bytes
   appended per user byte at 1M keys and 9.9 at 10M keys, at a startup
   distance of 20 MB (011-04, "Level 2 under load"); 180 to 670 bytes of
   stream a put at 200 to 1000 MB, with 10M and 50M keys (005-38).
5. Q8, the space bound with reclaim. Derive a bound for the algorithm as
   built (the cut point before the scan, iterations a quarter of the retain
   duration apart) and choose its budget f by the trade-off between write
   and store efficiency. Measured: reclaim adds 26 to 38 percent of the
   stream writes (011-04, W4).


Done when
---------

Each question has an answer: a bound stated and proved (in Lean, as T3 is
in item 007), a measurement that Frans accepts as the answer, or Frans's
word that it is dropped.


First step
----------

Ask Frans which of them matter now. Item 007, bounds on BergDB's costs, is
the natural home for Q1, Q3 and Q5 (its T4).


Frans's notes
-------------

2026-11-04, Frans's decision: 005-54 moves here as a long-term topic, not
to item 007 and not to a close.

* Not 007: item 007 (bounds) is concrete work with a plan, T3 proved and
  T4 a bound on D for startup. Five general theory questions would keep
  it open with no end in sight.
* Not a close: Q1 points at real behaviour, a tree that is split but never
  merged keeps its largest size after mass deletes. Q5 and Q8 already have
  measurements that could become the accepted answer.
* A question here that becomes a real theorem goes to item 007 then.


Log
---

2026-11-04. Moved here from 005-54 at Frans's decision, with 005-54's
contents, by Claude (Opus 5.5, Claude Code).
